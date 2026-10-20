import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
The classical affine-plane construction for the r^2 variant of Erdős 617.
Source: Erdős and Gyárfás, Discrete Mathematics 200 (1999), p. 80.
We use prime orders, which already give infinitely many parameters.
OpenAI Codex assisted with this formalization. No novelty claim is made.
-/

namespace Erdos617AffineProof
open Finset

variable (p : ℕ) [Fact p.Prime]

abbrev Point := ZMod p × ZMod p

def slope (a b : Point p) : ZMod p := (a.2 - b.2) / (a.1 - b.1)

lemma slope_symm (a b : Point p) : slope p a b = slope p b a := by
  unfold slope
  rw [show b.2 - a.2 = -(a.2 - b.2) by ring,
    show b.1 - a.1 = -(a.1 - b.1) by ring, neg_div_neg_eq]

noncomputable def coloring : Sym2 (Point p) → Fin p :=
  Sym2.lift ⟨fun a b => (ZMod.finEquiv p).symm (slope p a b),
    fun a b => congrArg (ZMod.finEquiv p).symm (slope_symm p a b)⟩

lemma intercept_fiber (k : ZMod p) (a b : Point p) (hab : a ≠ b)
    (he : a.2 - k * a.1 = b.2 - k * b.1) : slope p a b = k := by
  have hx : a.1 - b.1 ≠ 0 := by
    intro h
    have hfst : a.1 = b.1 := sub_eq_zero.mp h
    have hsnd : a.2 = b.2 := by rw [hfst] at he; linear_combination he
    exact hab (Prod.ext hfst hsnd)
  apply (div_eq_iff hx).mpr
  linear_combination he

theorem balanced (S : Finset (Point p)) (hS : S.card = p + 1) (k : Fin p) :
    ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring p s(u,v) = k := by
  classical
  let k' : ZMod p := ZMod.finEquiv p k
  have hc : (univ : Finset (ZMod p)).card < S.card := by
    simp only [card_univ, ZMod.card, hS]
    omega
  obtain ⟨a, ha, b, hb, hab, he⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
    (f := fun a : Point p => a.2 - k' * a.1) hc (fun _ _ => mem_univ _)
  refine ⟨a, ha, b, hb, hab, ?_⟩
  change (ZMod.finEquiv p).symm (slope p a b) = k
  rw [intercept_fiber p k' a b hab he]
  exact (ZMod.finEquiv p).symm_apply_apply k

omit [Fact p.Prime] in
theorem prime_parameter (hp : p.Prime) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V), Fintype.card V = p^2 ∧
      ∃ (c : Sym2 V → Fin p), ∀ S : Finset V, S.card = p + 1 →
        ∀ k : Fin p, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u,v) = k := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨Point p, inferInstance, inferInstance, ?_, coloring p, ?_⟩
  · simp [Point, Fintype.card_prod, ZMod.card, pow_two]
  · exact fun S hS k => balanced p S hS k

theorem r2 :
    {r : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V), Fintype.card V = r^2 ∧
      ∃ (c : Sym2 V → Fin r), ∀ S : Finset V, S.card = r + 1 →
        ∀ k : Fin r, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u,v) = k}.Infinite := by
  exact Nat.infinite_setOfPred_prime.mono (fun p hp => prime_parameter p hp)

end Erdos617AffineProof

#print axioms Erdos617AffineProof.balanced
#print axioms Erdos617AffineProof.r2
