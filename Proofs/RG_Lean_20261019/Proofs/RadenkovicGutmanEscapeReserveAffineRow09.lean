/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeReserveRawData
import Proofs.RadenkovicGutmanEscapeReducedReserve
import Proofs.RadenkovicGutmanNestedHornerNormalized
namespace Gebendorfer.RadenkovicGutman
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace EscapeReserveAffineRow09
def raw : NestedHorner.Poly 3 := NestedInteger.castPoly 3
  (EscapeReserveRawData.data.getD 9 [])
def unit : NestedHorner.Poly 3 := NestedInteger.castPoly 3
  (EscapeReducedReserve.data.getD 9 [])
def lower : Fin 3 → ℚ := ![653/2000,0,0]
def width : Fin 3 → ℚ := ![19347/2000,1,1]
theorem accepted : NestedHornerNormalized.affineCheck 3
    (NestedHorner.scale ((1/46 : ℚ)^9) raw) unit lower width=true := by
  decide +kernel
theorem evaluation (U a b : ℝ) :
    NestedHorner.eval unit ![U,a,b] =
      (1/46 : ℝ)^9*NestedHorner.eval raw ![(653/2000)+(19347/2000)*U,a,b] := by
  have h := NestedHornerNormalized.affineCheck_sound 3 _ _ lower width accepted ![U,a,b]
  rw [NestedHorner.eval_scale] at h
  have he : (fun i => (lower i : ℝ)+(width i : ℝ)*(![U,a,b] : Fin 3 → ℝ) i)=
      ![(653/2000)+(19347/2000)*U,a,b] := by
    ext i
    fin_cases i <;> norm_num [lower,width]
  rw [he] at h
  norm_num only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
  exact h
#print axioms accepted
#print axioms evaluation
end EscapeReserveAffineRow09
end
end Gebendorfer.RadenkovicGutman
