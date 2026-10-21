/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanTreeLeafInduction
import Mathlib.Data.Fintype.Option

/-! An explicit finite enumeration covering all finite rooted trees.
`Family n` enumerates all sequences of n leaf insertions, with the initial
vertex retained as root. It is redundant (n! entries), but complete up to a
root-preserving isomorphism. No canonical-tree census is assumed complete.
-/
namespace Gebendorfer.RadenkovicGutman.RootedTreeEnumeration
open TreeLeafInduction
set_option maxHeartbeats 0

def Vertices : ℕ → Type
  | 0 => Unit
  | n+1 => Option (Vertices n)

instance verticesFintype (n : ℕ) : Fintype (Vertices n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Option (Vertices n)))

instance verticesDecidableEq (n : ℕ) : DecidableEq (Vertices n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Option (Vertices n)))

def Family : ℕ → Type
  | 0 => Unit
  | n+1 => Family n × Vertices n

instance familyFintype (n : ℕ) : Fintype (Family n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Family n × Vertices n))

instance familyDecidableEq (n : ℕ) : DecidableEq (Family n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Family n × Vertices n))

def root : (n : ℕ) → Vertices n
  | 0 => ()
  | n+1 => some (root n)

def graph : {n : ℕ} → Family n → SimpleGraph (Vertices n)
  | 0, _ => ⊥
  | _+1, t => attach (graph t.1) t.2

def catalogue (n : ℕ) : Finset (Family n) := Finset.univ

@[simp] theorem card_vertices (n : ℕ) : Fintype.card (Vertices n)=n+1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    change Fintype.card (Option (Vertices n))=n+1+1
    rw [Fintype.card_option,ih]

theorem card_family (n : ℕ) : Fintype.card (Family n)=n.factorial := by
  induction n with
  | zero => decide
  | succ n ih =>
    change Fintype.card (Family n × Vertices n)=(n+1).factorial
    rw [Fintype.card_prod,ih,card_vertices,Nat.factorial_succ,Nat.mul_comm]

noncomputable section

def extensionIso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (v : V) : attach G v ≃g attach H (e v) where
  toEquiv := Equiv.optionCongr e.toEquiv
  map_rel_iff' := by
    intro a b
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b =>
        change e b=e v ↔ b=v
        exact e.injective.eq_iff
    | some a =>
      cases b with
      | none =>
        change e a=e v ↔ a=v
        exact e.injective.eq_iff
      | some b => exact e.map_adj_iff

def Representable (V : Type) (G : SimpleGraph V) (r : V) : Prop :=
  ∃ (n : ℕ) (t : Family n) (e : G ≃g graph t), e r=root n

theorem complete {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (hG : G.IsTree) : Representable V G r := by
  apply finite_tree_induction Representable ?_ ?_ ?_ G r hG
  · intro V _ G r
    let e : G ≃g graph (n := 0) () := {
      toEquiv := {
        toFun := fun _ => ()
        invFun := fun _ => r
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
      map_rel_iff' := by
        intro a b
        have hab : a=b := Subsingleton.elim _ _
        subst b
        exact iff_of_false (by trivial) G.irrefl }
    exact ⟨0,(),e,rfl⟩
  · intro V W G H e r hp
    obtain ⟨n,t,f,hr⟩ := hp
    refine ⟨n,t,e.symm.trans f,?_⟩
    simpa using hr
  · intro V G r v hp
    obtain ⟨n,t,e,hr⟩ := hp
    refine ⟨n+1,(t,e v),extensionIso e v,?_⟩
    change some (e r)=some (root n)
    rw [hr]

/-- Every actual rooted tree of the given order is represented in the complete
finite catalogue. Both the entire graph and its distinguished root are kept. -/
theorem complete_at_order {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (hG : G.IsTree) (n : ℕ)
    (hcard : Fintype.card V=n+1) :
    ∃ t ∈ catalogue n, ∃ e : G ≃g graph t, e r=root n := by
  obtain ⟨m,t,e,hr⟩ := complete G r hG
  have hc := Fintype.card_congr e.toEquiv
  rw [card_vertices,hcard] at hc
  have hmn : m=n := by omega
  subst m
  exact ⟨t,Finset.mem_univ _,e,hr⟩

#print axioms card_vertices
#print axioms card_family
#print axioms extensionIso
#print axioms complete
#print axioms complete_at_order
end
end Gebendorfer.RadenkovicGutman.RootedTreeEnumeration
