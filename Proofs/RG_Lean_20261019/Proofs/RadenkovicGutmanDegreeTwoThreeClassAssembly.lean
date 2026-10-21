/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanOriginalAssembly
import Proofs.RadenkovicGutmanDegreeTwoThreeThresholds

/-! Exact assembly for the original degree-two/three split. Concrete class
functions, their bounds and payments, and all finite cases remain premises. -/
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeClassAssembly
open SimpleGraph CoreQuotient ActualFusionIntegral OriginalAssembly
open ArmClasses DegreeTwoThreeThresholds Set MeasureTheory
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem table2_symmetric : ∀ c e : Fin 5, threshold2 c e=threshold2 e c := by decide +kernel
theorem table3_symmetric : ∀ c e : Fin 5, threshold3 c e=threshold3 e c := by decide +kernel

def cutoff (d : ℕ) (c : Fin 5 × Fin 5) : ℕ :=
  if d=2 then threshold2 c.1 c.2 else threshold3 c.1 c.2

theorem cutoff_pair (d p q : ℕ) : cutoff d (ClassEnvelope.pair p q)=threshold d p q := by
  unfold ClassEnvelope.pair
  split_ifs
  · rfl
  · unfold cutoff threshold
    split_ifs
    · exact table2_symmetric _ _
    · exact table3_symmetric _ _

theorem cutoff_positive (d : ℕ) (c : Fin 5 × Fin 5) : 0<cutoff d c := by
  unfold cutoff
  split_ifs
  · exact table2_positive c.1 c.2
  · exact table3_positive c.1 c.2

def Payments (d : ℕ) (B : (Fin 5 × Fin 5) → ℝ → ℝ) : Prop :=
  ∀ c ∈ unordered, (2 : ℝ)/(cutoff d c : ℝ)<
    (1/Real.pi)*(∫ y : ℝ in Ioi 0, B c y)

theorem paid_mean_positive (m d : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hdegree : C.degree u=d) (hd : d=2 ∨ d=3)
    (B : (Fin 5 × Fin 5) → ℝ → ℝ) (hB : ClassEnvelope.Bounds d B)
    (hBi : ∀ c ∈ unordered, IntegrableOn (B c) (Ioi 0)) (hPay : Payments d B)
    (hN : threshold d p q ≤ order C p q) : 0<meanIntegral C u p q := by
  have hroot : 1 ≤ C.degree u := by rcases hd with h | h <;> omega
  have hI := ClassEnvelope.integral_lower C u p q d hdegree B hB hBi
  have hpaid := hPay (ClassEnvelope.pair p q) (ClassEnvelope.pair_mem p q)
  rw [cutoff_pair] at hpaid
  have hpos := cutoff_positive d (ClassEnvelope.pair p q)
  rw [cutoff_pair] at hpos
  have hstrict := strict_of_cutoff_reserve C u p q (threshold d p q) hT hroot hpos hN
    (lt_of_lt_of_le hpaid hI)
  exact (strict_iff_mean_integral_pos C u p q hT hroot).mp hstrict

def FiniteCases : Prop :=
  ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → (C.degree u=2 ∨ C.degree u=3) →
    order C p q<threshold (C.degree u) p q → 0<meanIntegral C u p q

/-- These premises retain all thirty class payments and the complete original
finite range; no uniform cutoff substitutes for the individual thresholds. -/
theorem input_family_of_certificates
    (B : ℕ → (Fin 5 × Fin 5) → ℝ → ℝ)
    (hB : ∀ d, (d=2 ∨ d=3) → ClassEnvelope.Bounds d (B d))
    (hBi : ∀ d, (d=2 ∨ d=3) → ∀ c ∈ unordered, IntegrableOn (B d c) (Ioi 0))
    (hPay : ∀ d, (d=2 ∨ d=3) → Payments d (B d)) (hFinite : FiniteCases)
    (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : C.degree u=2 ∨ C.degree u=3) :
    0<meanIntegral C u p q := by
  by_cases hcut : order C p q<threshold (C.degree u) p q
  · exact hFinite m C u p q hT hd hcut
  · exact paid_mean_positive m (C.degree u) C u p q hT rfl hd
      (B (C.degree u)) (hB _ hd) (hBi _ hd) (hPay _ hd) (by omega)

#print axioms table2_symmetric
#print axioms table3_symmetric
#print axioms cutoff_pair
#print axioms cutoff_positive
#print axioms paid_mean_positive
#print axioms input_family_of_certificates
end
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeClassAssembly
