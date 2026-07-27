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

The remaining fidelity endpoint for #7884 is a public degreewise isomorphism from the external
total-complex terms (whose second resolution is concentrated in degree zero) to the literal free
modules `SV ⊗ ⋀ⁱ V ⊗ SV`, followed by the corresponding `Module.Free` theorem.
