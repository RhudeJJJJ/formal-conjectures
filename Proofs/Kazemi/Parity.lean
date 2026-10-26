module

public import Proofs.Kazemi.Geometry
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.NormNum

/-! # Binary syndromes, parity, and the extra-coordinate projection

Coordinate sums in exponent-two additive groups provide both the Hamming
syndrome and the bipartition of a Boolean cube.
-/

@[expose] public section
namespace Kazemi.Certificate
open Finset
variable {ι : Type*}

def zeroWord : Vertex ι := fun _ => false
def wordXor (x y : Vertex ι) : Vertex ι := fun i => Bool.xor (x i) (y i)

@[simp] theorem wordXor_twice (x y : Vertex ι) : wordXor (wordXor x y) y = x := by
  funext i
  change Bool.xor (Bool.xor (x i) (y i)) (y i) = x i
  cases x i <;> cases y i <;> rfl

@[simp] theorem wordXor_zero (x : Vertex ι) : wordXor x zeroWord = x := by
  funext i
  change Bool.xor (x i) false = x i
  cases x i <;> rfl

section Coordinate
variable [DecidableEq ι]

def singleWord (i : ι) : Vertex ι := Function.update zeroWord i true

theorem flip_eq_wordXor_single (x : Vertex ι) (i : ι) :
    flip x i = wordXor x (singleWord i) := by
  funext j
  by_cases hj : j = i
  · subst j
    cases hx : x i <;> simp [flip, wordXor, singleWord, hx]
  · simp [flip, wordXor, singleWord, zeroWord, hj]

end Coordinate

section Sums
variable [Fintype ι]
variable {β : Type*} [AddCommGroup β]

def bitSum (col : ι → β) (x : Vertex ι) : β := ∑ i, if x i then col i else 0

@[simp] theorem bitSum_zero (col : ι → β) : bitSum col zeroWord = 0 := by
  simp [bitSum, zeroWord]

theorem bitSum_xor (ht : ∀ b : β, b + b = 0) (col : ι → β) (x y : Vertex ι) :
    bitSum col (wordXor x y) = bitSum col x + bitSum col y := by
  rw [bitSum, bitSum, bitSum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  cases hx : x i <;> cases hy : y i <;> simp [wordXor, hx, hy, ht]

variable [DecidableEq ι]

@[simp] theorem bitSum_single (col : ι → β) (i : ι) : bitSum col (singleWord i) = col i := by
  rw [bitSum, sum_eq_single i]
  · simp [singleWord]
  · intro j hj hji
    simp [singleWord, zeroWord, hji]
  · intro hi
    exact False.elim (hi (mem_univ i))

theorem bitSum_flip (ht : ∀ b : β, b + b = 0) (col : ι → β) (x : Vertex ι) (i : ι) :
    bitSum col (flip x i) = bitSum col x + col i := by
  rw [flip_eq_wordXor_single, bitSum_xor ht, bitSum_single]

end Sums

theorem zmod_two_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod_two_cases a with rfl | rfl <;> decide

theorem zmod_two_add_one_of_ne {a b : ZMod 2} (h : a ≠ b) : a + 1 = b := by
  rcases zmod_two_cases a with rfl | rfl <;>
    rcases zmod_two_cases b with rfl | rfl
  all_goals first | exact False.elim (h rfl) | decide

section Parity
variable [Fintype ι] [DecidableEq ι]

def parity (x : Vertex ι) : ZMod 2 := bitSum (fun _ => 1) x

theorem parity_flip (x : Vertex ι) (i : ι) : parity (flip x i) = parity x + 1 :=
  bitSum_flip zmod_two_add_self _ x i

theorem parity_of_adj {x y : Vertex ι} (h : (cube ι).Adj x y) : parity y = parity x + 1 := by
  obtain ⟨i, rfl⟩ := (adj_iff_flip x y).1 h
  exact parity_flip x i

theorem parity_ne_of_adj {x y : Vertex ι} (h : (cube ι).Adj x y) : parity x ≠ parity y := by
  rw [parity_of_adj h]
  intro he
  have he' : parity x + 0 = parity x + 1 := (add_zero _).trans he
  exact zero_ne_one (add_left_cancel he')

def restrict (x : Vertex (Option ι)) : Vertex ι := fun i => x (some i)
def extend (x : Vertex ι) (b : Bool) : Vertex (Option ι) := fun i => i.elim b x

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem restrict_extend (x : Vertex ι) (b : Bool) : restrict (extend x b) = x := rfl

omit [Fintype ι] in
@[simp] theorem restrict_flip_none (x : Vertex (Option ι)) :
    restrict (flip x none) = restrict x := by
  funext i
  simp [restrict, flip]

omit [Fintype ι] in
theorem restrict_flip_some (x : Vertex (Option ι)) (i : ι) :
    restrict (flip x (some i)) = flip (restrict x) i := by
  funext j
  by_cases hj : j = i
  · subst j; simp [restrict, flip]
  · simp [restrict, flip, hj]

theorem exists_parity_lift (x : Vertex ι) (p : ZMod 2) :
    ∃ y : Vertex (Option ι), restrict y = x ∧ parity y = p := by
  let y := extend x false
  by_cases hp : parity y = p
  · exact ⟨y, rfl, hp⟩
  · refine ⟨flip y none, ?_, ?_⟩
    · rw [restrict_flip_none]
      rfl
    · rw [parity_flip]
      exact zmod_two_add_one_of_ne hp

omit [DecidableEq ι] in
theorem parity_parts_card (S : Finset (Vertex ι)) :
    (S.filter (fun x => parity x = 0)).card + (S.filter (fun x => parity x = 1)).card = S.card := by
  have he : S.filter (fun x => parity x = 1) = S.filter (fun x => ¬parity x = 0) := by
    ext x
    rcases zmod_two_cases (parity x) with h | h <;> simp [h]
  rw [he]
  exact card_filter_add_card_filter_not (s := S) (fun x => parity x = 0)

end Parity
end Kazemi.Certificate
