/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeReserveRawData
import Proofs.RadenkovicGutmanEscapeReducedReserve
import Proofs.RadenkovicGutmanNestedHornerNormalized
namespace Gebendorfer.RadenkovicGutman.EscapeReserveRawAffine
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
def lower : Fin 4 → ℚ := ![0,653/2000,0,0]
def width : Fin 4 → ℚ := ![1/46,19347/2000,1,1]
theorem accepted : NestedHornerNormalized.affineCheck 4
    (NestedInteger.castPoly 4 EscapeReserveRawData.data)
    (NestedInteger.castPoly 4 EscapeReducedReserve.data) lower width = true := by decide +kernel
theorem evaluation (H U a b : ℝ) :
    NestedHorner.eval (NestedInteger.castPoly 4 EscapeReducedReserve.data) ![H,U,a,b] =
      NestedHorner.eval (NestedInteger.castPoly 4 EscapeReserveRawData.data)
        ![H/46,(653/2000)+(19347/2000)*U,a,b] := by
  have h := NestedHornerNormalized.affineCheck_sound 4 _ _ lower width accepted ![H,U,a,b]
  have he : (fun i => (lower i : ℝ)+(width i : ℝ)*(![H,U,a,b] : Fin 4 → ℝ) i) =
      ![H/46,(653/2000)+(19347/2000)*U,a,b] := by
    ext i
    fin_cases i <;> norm_num [lower,width,div_eq_mul_inv,mul_comm]
  rwa [he] at h
#print axioms accepted
#print axioms evaluation
end
end Gebendorfer.RadenkovicGutman.EscapeReserveRawAffine
