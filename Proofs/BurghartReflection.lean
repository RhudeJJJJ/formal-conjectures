import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic.Ring

/-! # BurghartReflection
Exact-definition certificate for Burghart Conjecture 20.
All finite computations are checked by the Lean kernel. -/

set_option Elab.async false
namespace BurghartReflection
open Finset
abbrev Key := ℕ × ℕ × ℕ
abbrev Rep := Key →₀ ℤ

def add (p q : Rep) : Rep where
  support := (p.support ∪ q.support).filter fun k => p k + q k ≠ 0
  toFun k := p k + q k
  mem_support_toFun k := by
    simp only [mem_filter, mem_union, Finsupp.mem_support_iff]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_,h⟩
      by_cases hp : p k = 0
      · right
        intro hq
        exact h (by simp [hp,hq])
      · exact Or.inl hp

def single (k : Key) (c : ℤ) : Rep where
  support := if c = 0 then ∅ else {k}
  toFun j := if j = k then c else 0
  mem_support_toFun j := by
    by_cases hc : c = 0 <;> by_cases hj : j = k <;> simp [hc,hj]

theorem add_eq (p q : Rep) : add p q = p + q := by
  ext k
  rfl
theorem single_eq (k : Key) (c : ℤ) : single k c = Finsupp.single k c := by
  ext j
  simp [single, Finsupp.single_apply, eq_comm]

instance : Std.Associative add := ⟨by intro p q r; simp only [add_eq,add_assoc]⟩
instance : Std.Commutative add := ⟨by intro p q; simp only [add_eq,add_comm]⟩

def sum {α : Type*} (s : Finset α) (f : α → Rep) : Rep := s.fold add 0 f

theorem sum_eq {α : Type*} (s : Finset α) (f : α → Rep) : sum s f = ∑ x ∈ s, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sum]
  | @insert a s ha ih =>
    simp only [sum, Finset.fold_insert ha, Finset.sum_insert ha]
    rw [add_eq]
    exact congrArg (fun q => f a + q) ih

noncomputable def eval (p : Rep) : MvPolynomial (Fin 3) ℤ :=
  p.sum fun k c => MvPolynomial.C c * MvPolynomial.X 0 ^ k.1 *
    MvPolynomial.X 1 ^ k.2.1 * MvPolynomial.X 2 ^ k.2.2

theorem eval_add_std (p q : Rep) : eval (p + q) = eval p + eval q := by
  apply Finsupp.sum_add_index
  · intro k _
    simp
  · intro k _ a b
    simp only [map_add, add_mul]

theorem eval_add (p q : Rep) : eval (add p q) = eval p + eval q := by
  rw [add_eq,eval_add_std]

theorem eval_single (k : Key) (c : ℤ) : eval (single k c) =
    MvPolynomial.C c * MvPolynomial.X 0 ^ k.1 *
      MvPolynomial.X 1 ^ k.2.1 * MvPolynomial.X 2 ^ k.2.2 := by
  rw [single_eq]
  apply Finsupp.sum_single_index
  simp

theorem eval_zero : eval 0 = 0 := by simp [eval]

theorem eval_sum {α : Type*} (s : Finset α) (f : α → Rep) :
    eval (sum s f) = ∑ a ∈ s, eval (f a) := by
  classical
  rw [sum_eq]
  induction s using Finset.induction_on with
  | empty => simp [eval_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha, eval_add_std,ih]

example : add (single (0,1,2) 3) (single (0,1,2) (-3)) = (0 : Rep) := by decide +kernel
#print axioms eval_sum
end BurghartReflection
