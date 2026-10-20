import FormalConjectures.WrittenOnTheWallII.GraphConjecture340

/-!
Kernel-checked refutation of WOWII 340 using the explicit double broom D(5,5).
The mathematical construction and packings are from Jonas J. Gebendorfer's
manuscript of October 17, 2026, Theorem 4.3. OpenAI Codex assisted with Lean.
This certificate does not assert the exhaustive census or its minimality claim.
-/

namespace WOWII340Proof
open SimpleGraph Finset WrittenOnTheWallII.GraphConjecture340

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def parent : Fin 22 → Fin 22 := ![0,0,1,2,3,4,5,6,7,8,9,10,0,0,0,0,0,11,11,11,11,11]

def doubleBroom : SimpleGraph (Fin 22) where
  Adj v w := v ≠ w ∧ (parent v = w ∨ parent w = v)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel doubleBroom.Adj :=
  inferInstanceAs (DecidableRel fun v w => v ≠ w ∧ (parent v = w ∨ parent w = v))

theorem parent_lt : ∀ v : Fin 22, v ≠ 0 → (parent v).val < v.val := by decide

theorem reaches_zero (v : Fin 22) : doubleBroom.Reachable v 0 := by
  have aux : ∀ n : ℕ, ∀ v : Fin 22, v.val = n → doubleBroom.Reachable v 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw
      by_cases hz : w = 0
      · subst w
        exact .refl 0
      have hp := parent_lt w hz
      have ha : doubleBroom.Adj w (parent w) := by
        refine ⟨?_, Or.inl rfl⟩
        intro he
        have hv := congrArg Fin.val he
        omega
      exact ha.reachable.trans (ih (parent w).val (by omega) (parent w) rfl)
  exact aux v.val v rfl

theorem doubleBroom_connected : doubleBroom.Connected :=
  ⟨fun u v => (reaches_zero u).trans (reaches_zero v).symm⟩

theorem doubleBroom_tree : doubleBroom.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨doubleBroom_connected, ?_⟩
  have he : doubleBroom.edgeFinset.card = 21 := by decide
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, he,
    Nat.card_eq_fintype_card]
  decide

def totalSet : Finset (Fin 22) := {0,1,2,3,6,7,10,11}
def dominatingSet : Finset (Fin 22) := {0,3,6,9,11}

theorem totalSet_total : doubleBroom.IsTotalDominating (totalSet : Set (Fin 22)) := by
  change ∀ v : Fin 22, ∃ w ∈ totalSet, doubleBroom.Adj v w
  decide

theorem dominatingSet_dominates : doubleBroom.IsDominating (dominatingSet : Set (Fin 22)) := by
  change ∀ v : Fin 22, v ∈ dominatingSet ∨ ∃ w ∈ dominatingSet, doubleBroom.Adj v w
  decide

def openPacking : Fin 8 → Fin 22 := ![12,0,3,4,7,8,11,17]
def closedPacking : Fin 5 → Fin 22 := ![12,2,5,8,11]

theorem openPacking_disjoint : ∀ i j v,
    doubleBroom.Adj (openPacking i) v → doubleBroom.Adj (openPacking j) v → i = j := by
  decide

theorem closedPacking_disjoint : ∀ i j v,
    (v = closedPacking i ∨ doubleBroom.Adj (closedPacking i) v) →
    (v = closedPacking j ∨ doubleBroom.Adj (closedPacking j) v) → i = j := by
  decide

theorem total_lower (D : Finset (Fin 22))
    (hD : doubleBroom.IsTotalDominating (D : Set (Fin 22))) : 8 ≤ D.card := by
  classical
  have hex : ∀ i : Fin 8, ∃ v : {v // v ∈ D}, doubleBroom.Adj (openPacking i) v := by
    intro i
    obtain ⟨v, hv, hadj⟩ := hD (openPacking i)
    exact ⟨⟨v, hv⟩, hadj⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    apply openPacking_disjoint i j (f i) (hf i)
    simpa only [hij] using hf j
  simpa using Fintype.card_le_of_injective f hinj

theorem domination_lower (D : Finset (Fin 22))
    (hD : doubleBroom.IsDominating (D : Set (Fin 22))) : 5 ≤ D.card := by
  classical
  have hex : ∀ i : Fin 5, ∃ v : {v // v ∈ D},
      (v : Fin 22) = closedPacking i ∨ doubleBroom.Adj (closedPacking i) v := by
    intro i
    rcases hD (closedPacking i) with hi | ⟨v,hv,hadj⟩
    · exact ⟨⟨_,hi⟩, Or.inl rfl⟩
    · exact ⟨⟨v,hv⟩, Or.inr hadj⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    apply closedPacking_disjoint i j (f i) (hf i)
    simpa only [hij] using hf j
  simpa using Fintype.card_le_of_injective f hinj

theorem totalDomination_eq : doubleBroom.totalDominationNumber = 8 := by
  have hup : doubleBroom.totalDominationNumber ≤ 8 :=
    Nat.sInf_le ⟨totalSet, totalSet_total, by decide⟩
  have hne : {n | ∃ D : Finset (Fin 22), doubleBroom.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨8, totalSet, totalSet_total, by decide⟩
  obtain ⟨D, hD⟩ := Nat.sInf_mem hne
  have hlo := total_lower D hD.isTotalDominating
  have he := hD.card_eq
  change D.card = doubleBroom.totalDominationNumber at he
  omega

theorem domination_eq : doubleBroom.dominationNumber = 5 := by
  have hup : doubleBroom.dominationNumber ≤ 5 :=
    Nat.sInf_le ⟨dominatingSet, dominatingSet_dominates, by decide⟩
  obtain ⟨D, hD⟩ := doubleBroom.exists_isNDominatingSet_dominationNumber
  have hlo := domination_lower D hD.isDominating
  have he := hD.card_eq
  omega

theorem mode_eq : doubleBroom.smallestDegreeMode = 1 := by decide

def supportSet : Finset (Fin 22) := {0,11,12,13,14,15,16,17,18,19,20,21}

theorem supportSet_spec : leafSupportVertices doubleBroom = supportSet := by decide

abbrev SupportVertex := {v : Fin 22 // v ∈ supportSet}
def supportGraph : SimpleGraph SupportVertex := doubleBroom.induce (supportSet : Set (Fin 22))
instance : DecidableRel supportGraph.Adj := inferInstanceAs
  (DecidableRel fun u v : SupportVertex => doubleBroom.Adj u.val v.val)

def label (v : SupportVertex) : Fin 2 := if v.val = 0 ∨ v.val < 17 ∧ 12 ≤ v.val then 0 else 1
def representative (i : Fin 2) : SupportVertex := ⟨if i = 0 then 0 else 11, by fin_cases i <;> decide⟩

theorem label_representative : ∀ i, label (representative i) = i := by decide
theorem label_adj : ∀ u v, supportGraph.Adj u v → label u = label v := by decide
theorem reaches_representative : ∀ v : SupportVertex,
    v = representative (label v) ∨ supportGraph.Adj v (representative (label v)) := by decide

theorem component_count : Nat.card supportGraph.ConnectedComponent = 2 := by
  classical
  let f : Fin 2 → supportGraph.ConnectedComponent :=
    fun i => supportGraph.connectedComponentMk (representative i)
  have hinj : Function.Injective f := by
    intro i j hij
    obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hij
    have hwalk : ∀ {u v : SupportVertex}, supportGraph.Walk u v → label u = label v := by
      intro u v q
      induction q with
      | nil => rfl
      | cons h _ ih => exact (label_adj _ _ h).trans ih
    simpa only [label_representative] using hwalk p
  have hsurj : Function.Surjective f := by
    intro c
    refine Quot.inductionOn c ?_
    intro v
    refine ⟨label v, ?_⟩
    rcases reaches_representative v with h | h
    · exact (congrArg supportGraph.connectedComponentMk h).symm
    · exact SimpleGraph.ConnectedComponent.sound h.reachable.symm
  have hc := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  simpa using hc.symm

theorem components_eq : leafSupportComponents doubleBroom = 2 := by
  rw [leafSupportComponents, supportSet_spec]
  exact component_count

theorem conjecture340 : ¬ conjecture340Statement := by
  intro h
  have hh := h (Fin 22) doubleBroom doubleBroom_tree (by decide)
  rw [totalDomination_eq, components_eq, mode_eq, domination_eq] at hh
  omega

end WOWII340Proof

#print axioms WOWII340Proof.doubleBroom_tree
#print axioms WOWII340Proof.totalDomination_eq
#print axioms WOWII340Proof.domination_eq
#print axioms WOWII340Proof.mode_eq
#print axioms WOWII340Proof.components_eq
#print axioms WOWII340Proof.conjecture340
