import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.Rewrite
import Lean.Elab.Tactic.Simpa
import Lean.Elab.Tactic.RCases

/-! Integer counting for two balanced tree halves. -/

namespace WOWIIMedian
theorem poor_half_impossible (δ h i j d e t u : Nat)
    (hδ : 2 ≤ δ) (hh : 2 ≤ h) (ht : t ≤ 1) (hu : u ≤ 1) (htu : t + u ≤ 1)
    (hi : δ * i ≤ h - 1 + t) (hj : δ * j ≤ h - 1 + u)
    (hd : h - 1 ≤ δ * d) (he : h - 1 ≤ δ * e)
    (hg : d + e ≤ i + j + 1) (hstrict : 2 * h < δ * (d + e))
    (hsat : δ * d=h - 1 → i < d) (hpoor : d ≤ i) : False := by
  have hsub : h - 1 + 1=h := by omega
  have hdi : d=i := by
    apply Classical.byContradiction
    intro hn
    have hid : d + 1 ≤ i := by omega
    have hm := Nat.mul_le_mul_left δ hid
    simp only [Nat.mul_add,Nat.mul_one] at hm
    omega
  subst i
  have hprod : δ * d=h := by
    have hn : δ * d≠h - 1 := by intro heq;have hbad:=hsat heq;omega
    omega
  have ht1 : t=1 := by omega
  have hu0 : u=0 := by omega
  have hje : j + 1 ≤ d := by
    apply Classical.byContradiction
    intro hn
    have hjd : d ≤ j := by omega
    have hm := Nat.mul_le_mul_left δ hjd
    omega
  have hde : d ≤ e := by
    apply Classical.byContradiction
    intro hn
    have hed : e + 1 ≤ d := by omega
    have hm := Nat.mul_le_mul_left δ hed
    simp only [Nat.mul_add,Nat.mul_one] at hm
    omega
  have heq : d + e=2 * d := by omega
  rw [heq] at hstrict
  rw [Nat.mul_left_comm δ 2 d,hprod] at hstrict
  omega

theorem balanced_count_impossible (δ h i j d e t u : Nat)
    (hδ : 2 ≤ δ) (hh : 2 ≤ h) (ht : t ≤ 1) (hu : u ≤ 1) (htu : t + u ≤ 1)
    (hi : δ * i ≤ h - 1 + t) (hj : δ * j ≤ h - 1 + u)
    (hd : h - 1 ≤ δ * d) (he : h - 1 ≤ δ * e)
    (hg : d + e ≤ i + j + 1) (hstrict : 2 * h < δ * (d + e))
    (hsat : δ * d=h - 1 → i < d) (hsat' : δ * e=h - 1 → j < e) : False := by
  by_cases hp : d ≤ i
  · exact poor_half_impossible δ h i j d e t u hδ hh ht hu htu
      hi hj hd he hg hstrict hsat hp
  · have hp' : e ≤ j := by omega
    exact poor_half_impossible δ h j i e d u t hδ hh hu ht (by omega)
      hj hi he hd (by omega) (by simpa only [Nat.add_comm] using hstrict) hsat' hp'
end WOWIIMedian
