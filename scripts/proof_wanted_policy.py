"""Shared metadata policy for approved, non-blocking wanted theorems."""

from __future__ import annotations


APPROVED_STATUS = "scope_approved_proof_wanted"
APPROVAL_FIELD = "proof_wanted_approval"
APPROVAL_CLASSIFICATION = "approved_nonblocking"
APPROVAL_REQUIRED_FIELDS = {
    "classification",
    "declaration",
    "source",
    "scope_document",
    "scope_heading",
    "reason",
    "approved_by_issue",
}

# This is deliberately an exact ratchet, not a count. Adding or replacing an
# exception requires an explicit code change as well as scope documentation and
# item metadata, so a future wanted marker cannot inherit Ado's approval.
APPROVED_WANTED_ALLOWLIST = frozenset(
    {
        (
            "Chapter2/Remark2.9.3",
            "EtingofRepresentationTheory/Chapter2/Remark2_9_3.lean",
            "Etingof.ado",
        )
    }
)


def approval_identity(item: dict, approval: dict) -> tuple[str, str, str]:
    """The exact item/source/declaration identity reviewed by the policy."""
    return (item["id"], approval["source"], approval["declaration"])


def validate_item_approval(item: dict) -> list[str]:
    """Validate the approval-related fields of one progress item."""
    errors: list[str] = []
    item_id = item.get("id", "<unknown item>")
    status = item.get("status")
    approval = item.get(APPROVAL_FIELD)

    if status == "proof_wanted":
        errors.append(
            f"{item_id}: legacy status 'proof_wanted' is ambiguous; use an active "
            "proof status or the reviewed scope_approved_proof_wanted status"
        )

    if status != APPROVED_STATUS:
        if approval is not None:
            errors.append(f"{item_id}: {APPROVAL_FIELD} requires status {APPROVED_STATUS!r}")
        return errors

    if not isinstance(approval, dict):
        errors.append(f"{item_id}: missing object field {APPROVAL_FIELD}")
        return errors

    missing = APPROVAL_REQUIRED_FIELDS - approval.keys()
    if missing:
        errors.append(f"{item_id}: approval is missing {sorted(missing)}")
        return errors

    if approval["classification"] != APPROVAL_CLASSIFICATION:
        errors.append(
            f"{item_id}: approval classification must be {APPROVAL_CLASSIFICATION!r}"
        )
    for field in (
        "declaration",
        "source",
        "scope_document",
        "scope_heading",
        "reason",
    ):
        if not isinstance(approval[field], str) or not approval[field].strip():
            errors.append(f"{item_id}: approval field {field!r} must be nonempty text")
    if not isinstance(approval["approved_by_issue"], int) or approval["approved_by_issue"] <= 0:
        errors.append(f"{item_id}: approved_by_issue must be a positive issue number")
    if item.get("coverage") != "covered_full":
        errors.append(f"{item_id}: approved proof_wanted must retain coverage 'covered_full'")
    if item.get("sorry_free") is not True:
        errors.append(f"{item_id}: approved proof_wanted must record sorry_free: true")

    if not errors and approval_identity(item, approval) not in APPROVED_WANTED_ALLOWLIST:
        errors.append(
            f"{item_id}: approval identity is not in the explicit reviewed allowlist"
        )
    return errors
