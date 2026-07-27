## Issue #7884: Koszul bimodule resolution transport

The change-of-rings construction now reaches an actual projective resolution of `SV` with its
left/right `SV ⊗ SV` action:

- fixed the two extensionally equal but definitionally distinct scalar-restriction tensor
  instances with explicit pure-tensor constructors;
- proved the resulting target comparison equivariant for the full external action;
- transported the external tensor of the Koszul resolution and the regular degree-zero
  resolution through the shear equivalence;
- identified its target with the usual `SV` bimodule and packaged the result as
  `Etingof.koszulBimoduleResolution`.

The remaining fidelity endpoint is now complete:

- `Etingof.koszulBimoduleResolutionTermIso` identifies every resolution term with the literal
  module `(SV ⊗ ⋀ⁱ V) ⊗ SV`, equipped with the sheared enveloping-algebra action;
- `Etingof.koszulBimoduleResolution_free` proves these terms are free over `SV ⊗ SV` by an
  explicit reassociation and inverse-shear comparison with `(SV ⊗ SV) ⊗ ⋀ⁱ V`;
- `Etingof.koszulBimoduleResolution_quasiIso` exposes the augmentation quasi-isomorphism; and
- the `Etingof.Problem_8_2_10_iii*` wrappers collect the resolution, term identification,
  freeness, and quasi-isomorphism as the public exercise endpoints.
