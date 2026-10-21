/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeThresholds
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeThresholds
set_option maxHeartbeats 0

theorem table2_max : ∀ c e : Fin 5, threshold2 c e≤18 := by decide +kernel
theorem table3_max : ∀ c e : Fin 5, threshold3 c e≤18 := by decide +kernel

theorem threshold_max (d p q : ℕ) (hd : d=2 ∨ d=3) : threshold d p q≤18 := by
  rcases hd with rfl | rfl
  · simpa [threshold] using table2_max (ArmClasses.classify p) (ArmClasses.classify q)
  · simpa [threshold] using table3_max (ArmClasses.classify p) (ArmClasses.classify q)

/-- Every case below its own class cutoff has catalogue order at most eleven
and both recurrence indices in Fin 13. -/
theorem finite_parameters (m d p q : ℕ) (hd : d=2 ∨ d=3) (hdegree : d<m)
    (h : m+p+q+2<threshold d p q) : m≤11 ∧ p<13 ∧ q<13 := by
  have hm := unpaid_core_order d m p q hd h
  have ht := threshold_max d p q hd
  have hthree : 3≤m := by rcases hd with rfl | rfl <;> omega
  exact ⟨hm,by omega,by omega⟩

#print axioms table2_max
#print axioms table3_max
#print axioms threshold_max
#print axioms finite_parameters
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeThresholds
