/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPackedIntegerSemanticAffine
import Lean.Elab.Term

/-- Materialize only integer data. The separate equality and sign proofs are
checked by the kernel; this elaborator returns no proof or logical assumption. -/
elab "rg_integer_tensor% " t:term : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  let e ← Lean.instantiateMVars e
  Lean.Meta.withTransparency .all (Lean.Meta.reduce e)

namespace Gebendorfer.RadenkovicGutman.IntegerLiteral
set_option maxHeartbeats 0

theorem accepts_materialized {d : ℚ} {c₁ c₂ : Fin 5} (p : NormProgramPack.Pack d c₁ c₂)
    (reciprocal : Bool) (s L R : ℚ) (k n : ℕ) (deg : Fin 3 → ℕ) (l w : Fin 3 → ℚ)
    (a : NestedInteger.Poly 3)
    (ha : PackedIntegerClassCell.integerAffine p reciprocal s L deg l w=a)
    (hs : 0 < s) (hw : ∀ i, 0 < w i)
    (hr : PackedIntegerSemanticAffine.rawCheck (NormProgramPack.polynomial p reciprocal s L)
      (IntegerComputedClassCell.baseScale s L) deg=true)
    (hb : NestedInteger.bernsteinCheck 3 deg a=true)
    (hl : RationalLog.accepts L R k n=true) :
    FastNestedCellData.accepts d c₁ c₂
      (PackedIntegerClassCell.make p reciprocal s L R k n deg l w)=true := by
  apply PackedIntegerSemanticAffine.accepts_make p reciprocal s L R k n deg l w hs hw hr _ hl
  rw [ha]
  exact hb

#print axioms accepts_materialized
end Gebendorfer.RadenkovicGutman.IntegerLiteral
