module

public import Proofs.Kazemi.Code
public import Proofs.Kazemi.Prism
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # The conjecture's exact parameters and total-domination lower bound

The Option-indexed base cube has even dimension 2^n and the full cube has
dimension 2^n+1. All arithmetic is symbolic in n; no finite bound on n is used.
-/

@[expose] public section
namespace Kazemi.Certificate
open Finset

def gap (n : ℕ) : ℕ := 2^(2^n-n+1)

theorem two_pow_ge_twice (n : ℕ) (hn : 2 ≤ n) : 2*n ≤ 2^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; nlinarith

theorem gap_product (n : ℕ) : 2^n * gap n = 2^(2^n+1) := by
  have hn := pow_two_ge_self n
  have he : n + (2^n-n+1) = 2^n+1 := by omega
  rw [gap, ← pow_add, he]

theorem gap_ge_dimension (n : ℕ) (hn : 2 ≤ n) : Fintype.card (Index n) + 1 ≤ gap n := by
  have hpow := two_pow_ge_twice n hn
  have he : n+1 ≤ 2^n-n+1 := by omega
  have hg : (2 : ℕ)^(n+1) ≤ gap n := Nat.pow_le_pow_right (by decide) he
  rw [pow_succ] at hg
  rw [card_index]
  omega

theorem dimension_ge_five (n : ℕ) (hn : 2 ≤ n) : 5 ≤ Fintype.card (Index n) := by
  rw [card_index]
  have := two_pow_ge_twice n hn
  omega

theorem card_vertex_index (n : ℕ) : Fintype.card (Vertex (Index n)) = 2^(2^n+1) := by
  change Fintype.card (Index n → Bool) = _
  rw [Fintype.card_fun, Fintype.card_bool, card_index]

theorem count_identity (n : ℕ) :
    Fintype.card (Vertex (Index n)) + gap n = Fintype.card (Index n) * gap n := by
  rw [card_vertex_index, card_index, ← gap_product]
  ring

theorem card_base (n : ℕ) : Fintype.card (Option (Column n)) = 2^n := by
  simp only [Fintype.card_option, card_column]
  have hp : 0 < (2 : ℕ)^n := pow_pos (by decide) n
  omega

theorem even_base (n : ℕ) (hn : 2 ≤ n) : Even (Fintype.card (Option (Column n))) := by
  rw [card_base]
  refine ⟨2^(n-1), ?_⟩
  have he : n = (n-1)+1 := by omega
  calc
    (2 : ℕ)^n = 2^((n-1)+1) := congrArg (fun t => (2 : ℕ)^t) he
    _ = 2^(n-1)+2^(n-1) := by rw [pow_succ]; omega

theorem total_domination_bound (n : ℕ) (hn : 2 ≤ n)
    (S : Finset (Vertex (Index n))) (hS : TotallyDominates S) : gap n ≤ S.card := by
  have hm : 2 ≤ Fintype.card (Option (Column n)) := by
    rw [card_base]
    have := two_pow_ge_twice n hn
    omega
  have h := option_cube_total_domination hS hm (even_base n hn)
  rw [card_base, card_vertex_index, ← gap_product] at h
  by_contra hbad
  have hp : 0 < (2 : ℕ)^n := pow_pos (by decide) n
  have hlt := Nat.mul_lt_mul_of_pos_left (lt_of_not_ge hbad) hp
  exact (not_lt_of_ge h) hlt

end Kazemi.Certificate
