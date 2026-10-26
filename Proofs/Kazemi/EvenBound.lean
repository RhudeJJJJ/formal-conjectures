module

public import Proofs.Kazemi.CubeCounting
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-! # The even-dimensional domination bound

Van Wee's excess-count argument: every dominating set of an even-dimensional
Boolean cube of dimension m >= 2 has size at least 2^m / m. We use the
division-free inequality card(vertices) <= m * card(D).
-/

@[expose] public section
namespace Kazemi.Certificate
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inter_ball_card_sum (D : Finset (Vertex ι)) (v : Vertex ι) :
    (D ∩ closedBall v).card = ∑ w ∈ D, if w ∈ closedBall v then 1 else 0 := by
  rw [← sum_filter]
  have he : D.filter (fun w => w ∈ closedBall v) = D ∩ closedBall v := by ext w; simp
  rw [he]
  simp

theorem sum_inter_ball_swap (S D : Finset (Vertex ι)) :
    ∑ v ∈ S, (D ∩ closedBall v).card = ∑ c ∈ D, (S ∩ closedBall c).card := by
  simp_rw [inter_ball_card_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro c hc
  apply sum_congr rfl
  intro v hv
  simp only [closedBall_symm v c]

theorem weighted_ball_sum (S : Finset (Vertex ι)) (f : Vertex ι → ℕ) :
    ∑ v ∈ S, ∑ z ∈ closedBall v, f z =
      ∑ z : Vertex ι, (S ∩ closedBall z).card * f z := by
  classical
  calc
    _ = ∑ v ∈ S, ∑ z : Vertex ι, if z ∈ closedBall v then f z else 0 := by
      apply sum_congr rfl
      intro v hv
      rw [← sum_filter]
      congr 1
      ext z
      simp
    _ = ∑ z : Vertex ι, ∑ v ∈ S, if z ∈ closedBall v then f z else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro z hz
      have he : ∀ v, (if z ∈ closedBall v then f z else 0) =
          (if v ∈ closedBall z then f z else 0) := by
        intro v
        simp only [closedBall_symm v z]
      simp_rw [he]
      rw [← sum_filter]
      have hf : S.filter (fun v => v ∈ closedBall z) = S ∩ closedBall z := by ext v; simp
      rw [hf]
      simp

theorem even_finset_sum {α : Type*} (S : Finset α) (f : α → ℕ)
    (hf : ∀ x ∈ S, Even (f x)) : Even (∑ x ∈ S, f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
    rw [sum_insert hx]
    exact (hf x (by simp)).add (ih (fun y hy => hf y (by simp [hy])))

theorem even_dimension_domination {D : Finset (Vertex ι)} (hD : Dominates D)
    (hm : 2 ≤ Fintype.card ι) (heven : Even (Fintype.card ι)) :
    Fintype.card (Vertex ι) ≤ Fintype.card ι * D.card := by
  classical
  let m := Fintype.card ι
  let N := Fintype.card (Vertex ι)
  let k : Vertex ι → ℕ := fun z => (D ∩ closedBall z).card
  let e : Vertex ι → ℕ := fun z => k z - 1
  let E := ∑ z : Vertex ι, e z
  have hk : ∀ z, 1 ≤ k z := fun z => (hD z).card_pos
  have hek : ∀ z, e z + 1 = k z := fun z => Nat.sub_add_cancel (hk z)
  have hinc : (∑ z : Vertex ι, k z) = (m + 1) * D.card := by
    have h := sum_inter_ball_swap univ D
    simpa [k, m, Nat.mul_comm] using h
  have heq : E + N = (m + 1) * D.card := by
    calc
      E + N = ∑ z : Vertex ι, (e z + 1) := by simp [E, N, sum_add_distrib]
      _ = ∑ z : Vertex ι, k z := sum_congr rfl fun z _ => hek z
      _ = _ := hinc
  let L : Vertex ι → ℕ := fun v => ∑ z ∈ closedBall v, e z
  have hlocal : ∀ v, v ∉ D → 1 ≤ L v := by
    intro v hv
    have hparity : Even (∑ z ∈ closedBall v, k z) := by
      change Even (∑ z ∈ closedBall v, (D ∩ closedBall z).card)
      rw [sum_inter_ball_swap]
      apply even_finset_sum
      intro c hc
      exact closedBall_inter_even (by intro h; subst c; exact hv hc)
    have hsum : L v + (m + 1) = ∑ z ∈ closedBall v, k z := by
      calc
        _ = ∑ z ∈ closedBall v, (e z + 1) := by simp [L, m, sum_add_distrib]
        _ = _ := sum_congr rfl fun z _ => hek z
    obtain ⟨a, ha⟩ := heven
    obtain ⟨b, hb⟩ := hparity
    change m = a + a at ha
    omega
  let O := univ \ D
  have hout : O.card + D.card = N := by
    simpa [O, N] using card_sdiff_add_card_eq_card (subset_univ D)
  have hlower : O.card ≤ ∑ v ∈ O, L v := by
    calc
      O.card = ∑ _v ∈ O, (1 : ℕ) := by simp
      _ ≤ _ := sum_le_sum fun v hv => hlocal v (mem_sdiff.1 hv).2
  have hupper : (∑ v ∈ O, L v) ≤ (m - 1) * E := by
    change (∑ v ∈ O, ∑ z ∈ closedBall v, e z) ≤ _
    rw [weighted_ball_sum]
    calc
      _ ≤ ∑ z : Vertex ι, (m - 1) * e z := by
        apply sum_le_sum
        intro z hz
        by_cases hez : e z = 0
        · simp [hez]
        · have hec : (O ∩ closedBall z).card + k z = m + 1 := by
            have hs : O ∩ closedBall z = closedBall z \ D := by
              ext w
              simp [O, and_comm]
            rw [hs]
            simpa [k, m, inter_comm] using card_sdiff_add_card_inter (closedBall z) D
          have hkc : 2 ≤ k z := by have := hek z; omega
          have hc : (O ∩ closedBall z).card ≤ m - 1 := by omega
          exact Nat.mul_le_mul_right (e z) hc
      _ = _ := by rw [← mul_sum]
  have hineq : N ≤ D.card + (m - 1) * E := by omega
  let a := m - 1
  have hma : m = a + 1 := by dsimp [a, m]; omega
  change N ≤ m * D.card
  rw [hma] at heq hineq ⊢
  have heq' : a * (E + N) = a * ((a + 1 + 1) * D.card) := congrArg (a * ·) heq
  have hmul : (a + 1) * N ≤ (a + 1) * ((a + 1) * D.card) := by nlinarith
  by_contra hn
  have hlt := Nat.mul_lt_mul_of_pos_left (lt_of_not_ge hn) (Nat.succ_pos a)
  exact (not_lt_of_ge hmul) hlt

end Kazemi.Certificate
