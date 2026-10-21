/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Logic.Equiv.Option

/-! A complete structural induction for finite rooted trees. A census can use
this theorem after checking its singleton, root-preserving isomorphisms and
every one-leaf extension. The stored numerical census alone is not such a check.
-/
namespace Gebendorfer.RadenkovicGutman.TreeLeafInduction
noncomputable section
open scoped Classical
set_option maxHeartbeats 0

def attach {V : Type} (G : SimpleGraph V) (v : V) : SimpleGraph (Option V) where
  Adj
    | some a, some b => G.Adj a b
    | none, some b => b=v
    | some a, none => a=v
    | none, none => False
  symm := by
    constructor
    intro a b h
    cases a <;> cases b <;> first | exact h | exact h.symm
  loopless := by
    constructor
    intro a
    cases a
    · exact id
    · exact G.irrefl

theorem exists_leaf_ne_root {V : Type} [Fintype V] [DecidableEq V]
    [Nontrivial V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) (r : V) : ∃ v, v≠r ∧ G.degree v=1 := by
  obtain ⟨a,b,hab,ha,hb⟩ := hG.exists_ne_and_degree_eq_one
  by_cases har : a=r
  · exact ⟨b,by intro h; exact hab (har.trans h.symm),hb⟩
  · exact ⟨a,har,ha⟩

def deletionIso {V : Type} [DecidableEq V] (G : SimpleGraph V) (v w : V)
    (hvw : G.Adj v w) (hw : ∀ x, G.Adj v x → x=w) :
    attach (G.induce {v}ᶜ) (⟨w,hvw.ne'⟩ : {x : V // x≠v}) ≃g G where
  toEquiv := Equiv.optionSubtypeNe v
  map_rel_iff' := by
    intro a b
    cases a with
    | none =>
      cases b with
      | none => exact iff_of_false G.irrefl id
      | some b =>
        change G.Adj v b.val ↔ b=⟨w,hvw.ne'⟩
        constructor
        · intro h; exact Subtype.ext (hw b.val h)
        · rintro rfl; exact hvw
    | some a =>
      cases b with
      | none =>
        change G.Adj a.val v ↔ a=⟨w,hvw.ne'⟩
        constructor
        · intro h; exact Subtype.ext (hw a.val h.symm)
        · rintro rfl; exact hvw.symm
      | some b => rfl

/-- Root-preserving leaf induction covers every finite rooted tree. -/
theorem finite_tree_induction
    (P : ∀ (V : Type), SimpleGraph V → V → Prop)
    (singleton : ∀ (V : Type) [Subsingleton V] (G : SimpleGraph V) (r : V), P V G r)
    (isomorphism : ∀ {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
      (e : G ≃g H) (r : V), P V G r → P W H (e r))
    (extension : ∀ {V : Type} (G : SimpleGraph V) (r v : V),
      P V G r → P (Option V) (attach G v) (some r))
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : V)
    (hG : G.IsTree) : P V G r := by
  classical
  have main : ∀ n, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (r : V), Fintype.card V=n → G.IsTree → P V G r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ G r hn hG
      by_cases hnt : Nontrivial V
      · let : Nontrivial V := hnt
        obtain ⟨v,hvr,hdeg⟩ := exists_leaf_ne_root G hG r
        obtain ⟨w,hvw,hw⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
        let W := {x : V // x≠v}
        let H : SimpleGraph W := G.induce {v}ᶜ
        let root : W := ⟨r,Ne.symm hvr⟩
        let parent : W := ⟨w,hvw.ne'⟩
        have ht : H.IsTree :=
          ⟨hG.connected.induce_compl_singleton_of_degree_eq_one hdeg,
            hG.isAcyclic.induce {v}ᶜ⟩
        have hcard := Fintype.card_congr (Equiv.optionSubtypeNe v)
        change Fintype.card (Option W)=Fintype.card V at hcard
        simp only [Fintype.card_option] at hcard
        have hsmall : Fintype.card W<n := by omega
        have hp := ih (Fintype.card W) hsmall W H root rfl ht
        have he := extension H root parent hp
        have hi := isomorphism (attach H parent) G (deletionIso G v w hvw hw) (some root) he
        exact hi
      · let : Subsingleton V := not_nontrivial_iff_subsingleton.mp hnt
        exact singleton V G r
  exact main (Fintype.card V) V G r rfl hG

#print axioms exists_leaf_ne_root
#print axioms deletionIso
#print axioms finite_tree_induction
end
end Gebendorfer.RadenkovicGutman.TreeLeafInduction
