/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeClassAssembly
import Proofs.RadenkovicGutmanActualArmSymmetry
import Proofs.RadenkovicGutmanPaidFixedClassIntegral

namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeDirectAssembly
open SimpleGraph CoreQuotient ActualFusionIntegral OriginalAssembly ArmClasses
open DegreeTwoThreeClassAssembly DegreeTwoThreeThresholds
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

/-- A reserve is tied to one degree and one physical unordered arm class.
Its threshold is exactly the original class table's threshold. -/
def ClassReserve (d : ℕ) (c : Fin 5 × Fin 5) : Prop :=
  ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    C.degree u=d → classify p=c.1 → classify q=c.2 →
    (2 : ℝ)/(cutoff d c : ℝ)<normalizedIntegral C u p q 2

theorem reserve_of_slices (d : ℕ) (hd : 1 ≤ d) (c : Fin 5 × Fin 5)
    (cs : List FastArmCoverIntegral.Slice)
    (hc : FastArmCoverIntegral.checkAt (d : ℚ) c.1 c.2 (1/1000) 1024 cs=true)
    (hb : PaidFixedClassIntegral.accepts (2/(cutoff d c : ℚ))
      (FastArmCoverIntegral.payment cs)=true) : ClassReserve d c := by
  intro m C u p q hdegree hp hq
  have h := PaidFixedClassIntegral.normalized_target C u p q d hd hdegree
    c.1 c.2 hp hq (2/(cutoff d c : ℚ)) cs hc hb
  simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast] using h

theorem reserve_all_pairs (d : ℕ)
    (hclasses : ∀ c ∈ unordered, ClassReserve d c)
    (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (hdegree : C.degree u=d) :
    (2 : ℝ)/(threshold d p q : ℝ)<normalizedIntegral C u p q 2 := by
  rw [← cutoff_pair d p q]
  have hc := hclasses (ClassEnvelope.pair p q) (ClassEnvelope.pair_mem p q)
  by_cases h : classify p ≤ classify q
  · simp only [ClassEnvelope.pair,if_pos h] at hc ⊢
    exact hc m C u p q hdegree rfl rfl
  · simp only [ClassEnvelope.pair,if_neg h] at hc ⊢
    rw [ActualArmSymmetry.normalized_swap_two C u p q]
    exact hc m C u q p hdegree rfl rfl

/-- Thirty checked class reserves plus the complete original finite range
discharge the original degree-two/three input without another envelope model. -/
theorem input_family
    (hclasses : ∀ d, (d=2 ∨ d=3) → ∀ c ∈ unordered, ClassReserve d c)
    (hfinite : DegreeTwoThreeClassAssembly.FiniteCases)
    (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : C.degree u=2 ∨ C.degree u=3) :
    0<meanIntegral C u p q := by
  by_cases hcut : order C p q<threshold (C.degree u) p q
  · exact hfinite m C u p q hT hd hcut
  · have hroot : 1 ≤ C.degree u := by rcases hd with h | h <;> omega
    have hpos := cutoff_positive (C.degree u) (ClassEnvelope.pair p q)
    rw [cutoff_pair] at hpos
    have hr := reserve_all_pairs (C.degree u) (hclasses _ hd) m C u p q rfl
    exact (strict_iff_mean_integral_pos C u p q hT hroot).mp
      (strict_of_cutoff_reserve C u p q (threshold (C.degree u) p q)
        hT hroot hpos (by omega) hr)

#print axioms reserve_of_slices
#print axioms reserve_all_pairs
#print axioms input_family
end
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeDirectAssembly
