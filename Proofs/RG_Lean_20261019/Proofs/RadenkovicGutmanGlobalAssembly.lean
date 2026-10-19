/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIsoEnergy
import Proofs.RadenkovicGutmanFusionTerminal

/-!
# Conditional global assembly of the RG path minimum

This module composes the actual fusion and terminal results with three explicit
inputs: finite base cases, nonpath source presentations, and strict fusion above
an order cutoff. It uses the actual Laplacian energy from Spectral, transported
by IsoEnergy. The singleton case is proved directly.

The three inputs are hypotheses, not verified certificates or new axioms.
The target quantifiers and equality convention follow PR #7399, statement commit
3654bf2bddc5217f904b7b85207b1091e833de49.
-/

namespace Gebendorfer.RadenkovicGutman.GlobalAssembly

open SimpleGraph CoreQuotient RewireTopology FusionDescent TreeTerminal IsoEnergy
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The minimum and equality conclusions on the original labelled vertex set. -/
def Conclusion {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  laplacianEnergy (pathGraph n) ≤ laplacianEnergy G ∧
    (laplacianEnergy G = laplacianEnergy (pathGraph n) ↔
      Nonempty (G ≃g pathGraph n))

/-- Finite coverage below the cutoff; order one is handled without this input. -/
def SmallOrders (N : ℕ) : Prop :=
  ∀ n, 2 ≤ n → n < N → ∀ G : SimpleGraph (Fin n), G.IsTree → Conclusion G

/-- The source is the given tree up to a specified graph isomorphism. -/
def DecomposesAbove (N : ℕ) : Prop :=
  ∀ n, N ≤ n → ∀ G : SimpleGraph (Fin n), G.IsTree →
    ¬Nonempty (G ≃g pathGraph n) →
      ∃ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
        1 ≤ C.degree u ∧ Nonempty (G ≃g source C u p q)

/-- Strict energy improvement for the actual source/fused pair above the cutoff. -/
def StrictFusionAbove (N : ℕ) : Prop :=
  ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    N ≤ Fintype.card (Fin m ⊕ Fin (p + 1) ⊕ Fin (q + 1)) →
    (source C u p q).IsTree → 1 ≤ C.degree u →
      laplacianEnergy (fused C u p q) < laplacianEnergy (source C u p q)

theorem singleton_conclusion (G : SimpleGraph (Fin 1)) : Conclusion G := by
  have heq : G = pathGraph 1 := by
    ext u v
    have h : v = u := Subsingleton.elim _ _
    subst v
    simp
  rw [heq]
  exact ⟨le_rfl, ⟨fun _ => ⟨Iso.refl _⟩, fun _ => rfl⟩⟩

/-- Relabel the actual fused graph back to Fin n, preserving energy and leaves. -/
theorem concrete_descent {N n : ℕ} (hD : DecomposesAbove N)
    (hF : StrictFusionAbove N) (hn : N ≤ n) (G : SimpleGraph (Fin n))
    (hT : G.IsTree) (hpath : ¬Nonempty (G ≃g pathGraph n)) :
    ∃ H : SimpleGraph (Fin n), H.IsTree ∧ leafCount H + 1 = leafCount G ∧
      laplacianEnergy H < laplacianEnergy G := by
  obtain ⟨m, C, u, p, q, hd, ⟨f⟩⟩ := hD n hn G hT hpath
  have hS : (source C u p q).IsTree := f.isTree_iff.mp hT
  have ht := fusion_tree_and_leaf_count C u p q hS hd
  have hnS : n = Fintype.card (Fin m ⊕ Fin (p + 1) ⊕ Fin (q + 1)) := by
    simpa only [Fintype.card_fin] using Fintype.card_congr f.toEquiv
  let W := Fin m ⊕ Fin (p + q + 2)
  have hnW : n = Fintype.card W := hnS.trans ht.2.1
  let e : Fin n ≃ W := (finCongr hnW).trans (Fintype.equivFin W).symm
  let H := (fused C u p q).comap e
  let g : H ≃g fused C u p q := Iso.comap e (fused C u p q)
  refine ⟨H, g.isTree_iff.mpr ht.1, ?_, ?_⟩
  · have hlG := leaf_count_iso f
    have hlH := leaf_count_iso g
    have hl := ht.2.2
    omega
  · calc
      laplacianEnergy H = laplacianEnergy (fused C u p q) := energy_eq g
      _ < laplacianEnergy (source C u p q) :=
        hF m C u p q (by rw [← hnS]; exact hn) hS hd
      _ = laplacianEnergy G := (energy_eq f).symm

/-- Leaf induction closes the minimum and its equality characterization together. -/
theorem conclusion_of_descent {n : ℕ} (hn : 2 ≤ n)
    (hstep : ∀ G : SimpleGraph (Fin n), G.IsTree →
      ¬Nonempty (G ≃g pathGraph n) →
        ∃ H : SimpleGraph (Fin n), H.IsTree ∧ leafCount H + 1 = leafCount G ∧
          laplacianEnergy H < laplacianEnergy G)
    (G : SimpleGraph (Fin n)) (hT : G.IsTree) : Conclusion G := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have main : ∀ k, ∀ T : SimpleGraph (Fin n), leafCount T = k → T.IsTree →
      Conclusion T := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro T hk hTree
      by_cases hleaf : leafCount T ≤ 2
      · have he := leaf_count_eq_two_add_excess T hTree
        have hl : leafCount T = 2 := by omega
        have hp : Nonempty (T ≃g pathGraph n) := by
          simpa only [Fintype.card_fin] using (tree_two_leaves_iff_path T hTree).mp hl
        obtain ⟨f⟩ := hp
        have hE := energy_eq f
        exact ⟨hE.symm.le, ⟨fun _ => ⟨f⟩, fun _ => hE⟩⟩
      · have hp : ¬Nonempty (T ≃g pathGraph n) := by
          intro hiso
          have hleaf' := (tree_two_leaves_iff_path T hTree).mpr
            (by simpa only [Fintype.card_fin] using hiso)
          omega
        obtain ⟨H, hHT, hL, hE⟩ := hstep T hTree hp
        have hlt : leafCount H < k := by omega
        have hIH := ih (leafCount H) hlt H rfl hHT
        have hstrict : laplacianEnergy (pathGraph n) < laplacianEnergy T :=
          lt_of_le_of_lt hIH.1 hE
        refine ⟨hstrict.le, ?_⟩
        constructor
        · intro heq
          exact ((ne_of_gt hstrict) heq).elim
        · intro hiso
          exact (hp hiso).elim
  exact main (leafCount G) G rfl hT

/-- The global targets follow from three explicit remaining inputs. -/
theorem universal_conclusion (N : ℕ) (hN : 2 ≤ N) (hsmall : SmallOrders N)
    (hD : DecomposesAbove N) (hF : StrictFusionAbove N)
    (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) (hT : G.IsTree) : Conclusion G := by
  by_cases hn1 : n = 1
  · subst n
    exact singleton_conclusion G
  have hn2 : 2 ≤ n := by omega
  by_cases hsmalln : n < N
  · exact hsmall n hn2 hsmalln G hT
  · apply conclusion_of_descent hn2 ?_ G hT
    intro T hTree hpath
    exact concrete_descent hD hF (by omega) T hTree hpath

theorem path_minimum_of_inputs (N : ℕ) (hN : 2 ≤ N) (hsmall : SmallOrders N)
    (hD : DecomposesAbove N) (hF : StrictFusionAbove N)
    (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) (hT : G.IsTree) :
    laplacianEnergy (pathGraph n) ≤ laplacianEnergy G :=
  (universal_conclusion N hN hsmall hD hF n hn G hT).1

theorem path_equality_of_inputs (N : ℕ) (hN : 2 ≤ N) (hsmall : SmallOrders N)
    (hD : DecomposesAbove N) (hF : StrictFusionAbove N)
    (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) (hT : G.IsTree) :
    laplacianEnergy G = laplacianEnergy (pathGraph n) ↔ Nonempty (G ≃g pathGraph n) :=
  (universal_conclusion N hN hsmall hD hF n hn G hT).2

#print axioms singleton_conclusion
#print axioms concrete_descent
#print axioms conclusion_of_descent
#print axioms universal_conclusion
#print axioms path_minimum_of_inputs
#print axioms path_equality_of_inputs

end
end Gebendorfer.RadenkovicGutman.GlobalAssembly
