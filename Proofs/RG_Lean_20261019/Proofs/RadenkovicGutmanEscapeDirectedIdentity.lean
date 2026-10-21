/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeDirectedData
import Proofs.RadenkovicGutmanEscapeDirectedEvaluation
import Proofs.RadenkovicGutmanCorrelatedEscape
import Proofs.RadenkovicGutmanCorrelatedEscapeReduction

/-! Exact original positively cleared polynomial identity; signs are separate. -/
namespace Gebendorfer.RadenkovicGutman.EscapeDirectedCertificate
open Set
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
abbrev data := EscapeDirectedData.data
abbrev degrees := EscapeDirectedData.degrees

def form (h x a b : ℝ) : ℝ := -h^8*x^10*(1+x^2)^6*CorrelatedEscape.directed (1/h) (x/h) (x/h+a*h/x) (x/h+b*h/x) (CorrelatedEscape.payment (1/h) x)

theorem data_identity (H U a b : ℝ) (hH : H ≠ 0)
    (hX : (653/2000 : ℝ)+(19347/2000 : ℝ)*U ≠ 0) :
    NestedHorner.eval (NestedInteger.castPoly 4 data) ![H,U,a,b] =
      (9519459831916749656232983908361175040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*form (H/46) ((653/2000)+(19347/2000)*U) a b := by
  change NestedHorner.eval (NestedInteger.castPoly 4 EscapeDirectedData.data) ![H,U,a,b] = _
  rw [EscapeDirectedEvaluation.data_eval]
  run_tac liftIO (IO.eprintln "RG_STAGE_TABLE_REWRITTEN")
  dsimp only [form]
  run_tac liftIO (IO.eprintln "RG_STAGE_FORM_UNFOLDED")
  rw [CorrelatedEscapeReduction.directed_reduced]
  run_tac liftIO (IO.eprintln "RG_STAGE_DIRECTED_REDUCED")
  have hh : (H/46 : ℝ) ≠ 0 := div_ne_zero hH (by norm_num)
  simp only [CorrelatedEscapeReduction.payment_reciprocal _ _ hh,
    CorrelatedEscapeReduction.radius_reciprocal _ _ hh hX]
  dsimp only [CorrelatedEscapeReduction.factorCore,CorrelatedEscapeReduction.factorLead,
    CorrelatedEscapeReduction.factorBase,CorrelatedEscapeReduction.factorHorizontal,
    CorrelatedEscapeReduction.factorVertical,CorrelatedEscapeReduction.errorWeight]
  run_tac liftIO (IO.eprintln "RG_STAGE_FACTORS_UNFOLDED")
  field_simp [hH,hX,show (1+((653/2000 : ℝ)+(19347/2000 : ℝ)*U)^2) ≠ 0 by positivity]
  run_tac liftIO (IO.eprintln "RG_STAGE_DENOMINATORS_CLEARED")
  ring

#print axioms data_identity
end
end Gebendorfer.RadenkovicGutman.EscapeDirectedCertificate
