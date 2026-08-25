#!/usr/bin/env python3
"""Validate and privately aggregate clean-room naming/docstring responses."""

from __future__ import annotations

import argparse
import json
import re
import unicodedata
from pathlib import Path


BANNED = re.compile(
    r"(?i)(etingof|introduction\s+to\s+representation\s+theory|"
    r"chapter\s*\d|section\s*\d|(?:theorem|problem|exercise)\s*\d+[._]\d+)"
)
LEAN_KEYWORDS = {
    "abbrev", "attribute", "axiom", "by", "class", "def", "deriving", "do",
    "else", "end", "example", "export", "extends", "false", "for", "forall",
    "from", "fun", "have", "if", "import", "in", "include", "inductive", "infix",
    "infixl", "infixr", "instance", "let", "macro", "match", "module", "mutual",
    "namespace", "noncomputable", "notation", "opaque", "open", "partial", "private",
    "protected", "public", "scoped", "section", "set_option", "show", "structure",
    "syntax", "theorem", "true", "universe", "variable", "where", "with",
}


def words(value: str) -> list[str]:
    normalized = unicodedata.normalize("NFKC", value).casefold()
    return re.findall(r"[^\W_]+", normalized, flags=re.UNICODE)


def ngrams(value: str, size: int) -> set[tuple[str, ...]]:
    tokens = words(value)
    return {tuple(tokens[index : index + size]) for index in range(len(tokens) - size + 1)}


def valid_lean_name(value: str) -> bool:
    if not value or value.startswith(".") or value.endswith(".") or ".." in value:
        return False
    return all(
        bool(re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*", segment))
        and segment not in LEAN_KEYWORDS
        for segment in value.split(".")
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("packets", type=Path)
    parser.add_argument("book_blobs", type=Path)
    parser.add_argument("private_mapping", type=Path)
    parser.add_argument("proposals", type=Path)
    args = parser.parse_args()

    packet_root = args.packets.resolve()
    index = json.loads((packet_root / "index.json").read_text(encoding="utf-8"))
    source_ngrams: set[tuple[str, ...]] = set()
    for path in args.book_blobs.rglob("*.md"):
        source_ngrams |= ngrams(path.read_text(encoding="utf-8"), 8)

    private_by_id = {}
    with args.private_mapping.open(encoding="utf-8") as stream:
        for line in stream:
            record = json.loads(line)
            private_by_id[record["temporary_id"]] = record

    errors: list[str] = []
    proposals: list[dict] = []
    seen_modules: dict[str, Path] = {}
    response_count = 0
    declaration_count = 0

    for index_record in index["packets"]:
        packet_path = packet_root / index_record["packet"]
        response_path = packet_path.with_name("response.json")
        if not response_path.exists():
            continue
        response_count += 1
        packet = json.loads(packet_path.read_text(encoding="utf-8"))
        response = json.loads(response_path.read_text(encoding="utf-8"))
        module_name = response.get("module_name")
        if not isinstance(module_name, str) or not valid_lean_name(module_name):
            errors.append(f"{response_path}: invalid module_name")
            continue
        if module_name == "RepresentationTheory" or module_name.startswith("RepresentationTheory."):
            errors.append(f"{response_path}: module_name must be relative to RepresentationTheory")
        if BANNED.search(module_name):
            errors.append(f"{response_path}: banned source marker in module_name")
        if module_name in seen_modules:
            errors.append(f"{response_path}: duplicate module_name also in {seen_modules[module_name]}")
        seen_modules[module_name] = response_path

        expected = {entry["temporary_id"] for entry in packet["declarations"]}
        entries = response.get("declarations")
        if not isinstance(entries, list):
            errors.append(f"{response_path}: declarations is not a list")
            continue
        actual = [entry.get("temporary_id") for entry in entries if isinstance(entry, dict)]
        if len(actual) != len(set(actual)) or set(actual) != expected:
            errors.append(f"{response_path}: declaration ID coverage mismatch")
            continue

        for entry in entries:
            temporary_id = entry["temporary_id"]
            new_name = entry.get("new_name")
            docstring = entry.get("docstring")
            if not isinstance(new_name, str) or not valid_lean_name(new_name):
                errors.append(f"{response_path}: {temporary_id} has invalid new_name")
                continue
            if not isinstance(docstring, str) or not docstring.strip() or len(docstring) > 2000:
                errors.append(f"{response_path}: {temporary_id} has invalid docstring")
                continue
            if BANNED.search(new_name) or BANNED.search(docstring):
                errors.append(f"{response_path}: {temporary_id} contains a banned source marker")
            overlap = ngrams(docstring, 8) & source_ngrams
            if overlap:
                phrase = " ".join(next(iter(overlap)))
                errors.append(f"{response_path}: {temporary_id} repeats source prose: {phrase!r}")
            if "[book-ref=" in docstring or "Etingof et al." in docstring:
                errors.append(f"{response_path}: {temporary_id} supplied an alignment line")
            private = private_by_id.get(temporary_id)
            if private is None:
                errors.append(f"{response_path}: {temporary_id} missing from private mapping")
                continue
            proposals.append(
                {
                    **private,
                    "new_module": f"RepresentationTheory.{module_name}",
                    "proposed_name": new_name,
                    "cleanroom_docstring": docstring.strip(),
                    "response": str(response_path.relative_to(packet_root)),
                }
            )
            declaration_count += 1

    proposal_by_id = {proposal["temporary_id"]: proposal for proposal in proposals}
    resolving: set[str] = set()

    def resolve_fqn(temporary_id: str) -> str | None:
        proposal = proposal_by_id.get(temporary_id)
        if proposal is None:
            return None
        existing = proposal.get("new_fqn")
        if existing is not None:
            return existing
        if temporary_id in resolving:
            errors.append(f"ownership cycle involving {temporary_id}")
            return None
        resolving.add(temporary_id)
        owner = proposal.get("owner_temporary_id")
        if owner is None:
            value = f"{proposal['new_module']}.{proposal['proposed_name']}"
        else:
            owner_fqn = resolve_fqn(owner)
            value = (
                f"{owner_fqn}.{proposal['proposed_name']}"
                if owner_fqn is not None
                else None
            )
        resolving.remove(temporary_id)
        proposal["new_fqn"] = value
        proposal["name_resolution_status"] = "resolved" if value is not None else "waiting_for_owner"
        return value

    seen_fqns: dict[str, str] = {}
    for proposal in proposals:
        new_fqn = resolve_fqn(proposal["temporary_id"])
        if new_fqn is None:
            continue
        owner_id = proposal.get("owner_temporary_id")
        if owner_id is not None:
            owner_fqn = resolve_fqn(owner_id)
            if owner_fqn is not None:
                owner_name = owner_fqn.rsplit(".", 1)[-1]
                if proposal["proposed_name"].split(".", 1)[0] == owner_name:
                    errors.append(
                        f"{proposal['response']}: {proposal['temporary_id']} repeats its "
                        f"owner name {owner_name!r}; nested names are relative"
                    )
        if new_fqn in seen_fqns:
            errors.append(
                f"duplicate new FQN for {proposal['temporary_id']} and {seen_fqns[new_fqn]}: {new_fqn}"
            )
        seen_fqns[new_fqn] = proposal["temporary_id"]

    if errors:
        raise SystemExit("\n".join(errors))
    args.proposals.parent.mkdir(parents=True, exist_ok=True)
    with args.proposals.open("w", encoding="utf-8") as stream:
        for proposal in sorted(proposals, key=lambda value: value["temporary_id"]):
            stream.write(json.dumps(proposal, sort_keys=True) + "\n")
    print(json.dumps({"responses": response_count, "declarations": declaration_count}))


if __name__ == "__main__":
    main()
