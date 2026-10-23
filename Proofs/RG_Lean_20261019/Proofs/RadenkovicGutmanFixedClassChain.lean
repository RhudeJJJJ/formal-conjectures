/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastArmCoverIntegral

namespace Gebendorfer.RadenkovicGutman.FixedClassChain
open FastArmCoverIntegral

def adjacent : ℚ → ℚ → List Slice → Bool
  | a,b,[] => decide (a=b)
  | a,b,c::cs => decide (c.lower=a) && adjacent c.upper b cs

theorem check_of_adjacent (d : ℚ) (c₁ c₂ : Fin 5) (a b : ℚ) (cs : List Slice)
    (hc : adjacent a b cs=true) (hs : ∀ c∈cs, accepts d c₁ c₂ c=true) :
    checkAt d c₁ c₂ a b cs=true := by
  induction cs generalizing a with
  | nil => exact hc
  | cons c cs ih =>
    have hh : decide (c.lower=a)=true ∧ adjacent c.upper b cs=true := by
      simpa only [adjacent,Bool.and_eq_true] using hc
    exact checked_cons d c₁ c₂ a b c cs (of_decide_eq_true hh.1)
      (hs c (by simp)) (ih c.upper hh.2 (fun z hz => hs z (by simp [hz])))

#print axioms check_of_adjacent
end Gebendorfer.RadenkovicGutman.FixedClassChain
