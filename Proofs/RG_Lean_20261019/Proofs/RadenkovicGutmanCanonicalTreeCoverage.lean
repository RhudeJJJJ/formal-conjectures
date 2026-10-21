/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRootedTreeEnumeration

/-! Finite, exact certificates for a reduced rooted-tree catalogue. A checked
transition covers every vertex of every preceding representative. Together with
the singleton and finite-tree induction this proves coverage of actual trees.
-/
namespace Gebendorfer.RadenkovicGutman.CanonicalTreeCoverage
open RootedTreeEnumeration
set_option maxHeartbeats 0

def label : {n : ℕ} → Vertices n → Fin (n+1)
  | 0, _ => 0
  | n+1, none => Fin.last (n+1)
  | _+1, some v => (label v).castSucc

def vertex : (n : ℕ) → ℕ → Vertices n
  | 0, _ => ()
  | n+1, i => if i=n+1 then none else some (vertex n i)

instance graphDecidable : {n : ℕ} → (t : Family n) → DecidableRel (graph t).Adj
  | 0, _, _, _ => isFalse id
  | _+1, t, some a, some b => graphDecidable t.1 a b
  | _+1, t, none, some b => inferInstanceAs (Decidable (b=t.2))
  | _+1, t, some a, none => inferInstanceAs (Decidable (a=t.2))
  | _+1, _, none, none => isFalse id

def acceptsIso {n : ℕ} (s t : Family n) (f : Vertices n → Vertices n) : Bool :=
  decide (Function.Bijective f ∧
    (∀ a b, (graph t).Adj (f a) (f b) ↔ (graph s).Adj a b) ∧ f (root n)=root n)

noncomputable def checkedIso {n : ℕ} (s t : Family n) (f : Vertices n → Vertices n)
    (h : acceptsIso s t f=true) : graph s ≃g graph t where
  toEquiv := Equiv.ofBijective f (of_decide_eq_true h).1
  map_rel_iff' := (of_decide_eq_true h).2.1 _ _

theorem checkedIso_root {n : ℕ} (s t : Family n) (f : Vertices n → Vertices n)
    (h : acceptsIso s t f=true) : checkedIso s t f h (root n)=root n :=
  (of_decide_eq_true h).2.2

structure Witness (n count : ℕ) where
  target : Fin count
  map : Vertices n → Vertices n

def checkStep (n : ℕ) (xs : List (Family n)) (ys : List (Family (n+1)))
    (w : Fin xs.length → Vertices n → Witness (n+1) ys.length) : Bool :=
  decide (∀ i v, acceptsIso (n := n+1) (xs.get i,v) (ys.get (w i v).target) (w i v).map=true)

theorem step_sound (n : ℕ) (xs : List (Family n)) (ys : List (Family (n+1)))
    (w : Fin xs.length → Vertices n → Witness (n+1) ys.length)
    (h : checkStep n xs ys w=true) (i : Fin xs.length) (v : Vertices n) :
    ∃ j : Fin ys.length, ∃ e : graph (n := n+1) (xs.get i,v) ≃g graph (ys.get j),
      e (root (n+1))=root (n+1) := by
  have hi := of_decide_eq_true h i v
  exact ⟨(w i v).target,checkedIso _ _ _ hi,checkedIso_root _ _ _ hi⟩

noncomputable section

theorem coversAllFamilies (C : ∀ n, List (Family n)) (N : ℕ)
    (base : ∃ i : Fin (C 0).length, (C 0).get i=())
    (step : ∀ n, n < N → ∀ i : Fin (C n).length, ∀ v : Vertices n,
      ∃ j : Fin (C (n+1)).length,
        ∃ e : graph (n := n+1) ((C n).get i,v) ≃g graph ((C (n+1)).get j),
          e (root (n+1))=root (n+1)) :
    ∀ n, n≤N → ∀ t : Family n, ∃ i : Fin (C n).length,
      ∃ e : graph t ≃g graph ((C n).get i), e (root n)=root n := by
  intro n
  induction n with
  | zero =>
    intro _ t
    obtain ⟨i,hi⟩ := base
    refine ⟨i,?_⟩
    rw [hi]
    cases t
    exact ⟨SimpleGraph.Iso.refl _,rfl⟩
  | succ n ih =>
    intro hn t
    obtain ⟨i,e,hr⟩ := ih (by omega) t.1
    obtain ⟨j,f,hf⟩ := step n (by omega) i (e t.2)
    refine ⟨j,(extensionIso e t.2).trans f,?_⟩
    change f (some (e (root n)))=root (n+1)
    rw [hr]
    exact hf

/-- Checked catalogue closure transfers to every actual rooted tree. -/
theorem actual_tree_covered (C : ∀ n, List (Family n)) (N : ℕ)
    (base : ∃ i : Fin (C 0).length, (C 0).get i=())
    (step : ∀ n, n < N → ∀ i : Fin (C n).length, ∀ v : Vertices n,
      ∃ j : Fin (C (n+1)).length,
        ∃ e : graph (n := n+1) ((C n).get i,v) ≃g graph ((C (n+1)).get j),
          e (root (n+1))=root (n+1))
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V)
    (hG : G.IsTree) (n : ℕ) (hn : n≤N) (hc : Fintype.card V=n+1) :
    ∃ i : Fin (C n).length, ∃ e : G ≃g graph ((C n).get i), e r=root n := by
  obtain ⟨t,_,e,hr⟩ := complete_at_order G r hG n hc
  obtain ⟨i,f,hf⟩ := coversAllFamilies C N base step n hn t
  refine ⟨i,e.trans f,?_⟩
  change f (e r)=root n
  rw [hr]
  exact hf

#print axioms checkedIso
#print axioms checkedIso_root
#print axioms step_sound
#print axioms coversAllFamilies
#print axioms actual_tree_covered
end
end Gebendorfer.RadenkovicGutman.CanonicalTreeCoverage
