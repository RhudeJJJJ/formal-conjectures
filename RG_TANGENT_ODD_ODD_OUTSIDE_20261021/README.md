# First original tangent parity polynomial

Jonas J. Gebendorfer. OpenAI Codex assisted with implementation and validation.

**PROVEN: the complete reconstructed odd/odd outside integer polynomial is nonnegative on [0,1]^4. The original geometric clearing identity and odd/odd outside sign are also PROVEN in the separate 68-module check.**

`TangentOddOddOutside.unit_box_nonneg` covers every vector v:Fin 4 -> Real with coordinates in [0,1]. Its degree vector is [12,26,4,4], with all 8,775 Bernstein coefficients. There is no graph or parameter sampling premise. [Run 39518437924](https://github.com/RhudeJJJJ/formal-conjectures/actions/runs/39518437924), job 118956138808, freshly exports all twelve local modules at [source 03c2cedc651269be0b82d44ad5fa3a2b36553c99](https://github.com/RhudeJJJJ/formal-conjectures/tree/03c2cedc651269be0b82d44ad5fa3a2b36553c99/Proofs/RG_Lean_20261019). It uses official Lean 4.33.1, pinned Mathlib, warnings as errors and only standard axioms.

The original producer bytes are pinned in `original_reconstruction.json`. Only their exact constructor functions were used; their main routines were not executed. The source cutoff remains 46, and the coordinates are H=46*h, C=2*c and the original two odd-arm parameters a,b. The positive integer coefficient scale is 11765324404956231737802752. The reconstruction requires the identity

    integerEval(46*h,2*c,a,b)
      = scale*h^2*c*(1-c^2)^10 * outside(1/h,y,y+a,y+b,c),
    y=4*c*h/(1-c^2).

That identity passed separately in run 39518879837 at source fb81f52369d5647ae1effd04a9adcaa4f7c0c320. Its completed 68-module closure has four fresh exports and 64 explicit prior-job exports. The original geometric odd/odd outside sign is proved after dividing by the positive clearing factors. The more general analytic outside proof covers every physical arm pair; see ../RG_LOWSTRIP_OUTSIDE_20261021/README.md. The constructor provenance alone was not used as proof. The original directed and full-reserve signs in this parity case, the other parity cases, the constant strip, all seven complete OriginalAssembly.Inputs families and the universal Lean theorem remain OPEN.

For a fresh check, run the supplied verify_extension.py with endpoint Proofs.RadenkovicGutmanTangentOddOddOutside and the pinned Mathlib checkout. Aletheion was untouched in this phase.
