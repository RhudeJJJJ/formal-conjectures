import Proofs.WOWII430Data
import Mathlib.Combinatorics.SimpleGraph.Diam
namespace WOWII430Proof
open SimpleGraph Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V]
def maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, G.degree w ≤ G.degree v
noncomputable def center (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter fun v => G.eccent v = G.radius
noncomputable def squareResidue (G : SimpleGraph V) : ℕ := by
  classical
  exact G.graphSquare.residue
noncomputable def inducedMaxDegree (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact (G.induce (S : Set V)).maxDegree
noncomputable def boundOn (G : SimpleGraph V) (S : Finset V) : ℕ :=
  G.maxLocalIndependence * squareResidue G + inducedMaxDegree G S

/-- Upper bound for every independent set contained in one open neighborhood. -/
lemma local_selection_bound (v : Fin 105) (I : Finset (Fin 105))
    (hI : witness.IsIndepSet (I : Set (Fin 105))) (hN : I ⊆ adjacency v) : I.card ≤ 20 := by
  classical
  let cap (c : Fin 105) := insert c ((outer ∩ adjacency v) \ adjacency c)
  have cap_bound : ∀ c ∈ clique, c ∈ adjacency v → (cap c).card ≤ 20 := by
    have hall : ∀ v c : Fin 105, c ∈ clique → c ∈ adjacency v →
        (insert c ((outer ∩ adjacency v) \ adjacency c)).card ≤ 20 := by decide
    exact hall v
  have outer_bound : (outer ∩ adjacency v).card ≤ 20 := by
    have hall : ∀ v : Fin 105, (outer ∩ adjacency v).card ≤ 20 := by decide
    exact hall v
  by_cases hc : (I ∩ clique).Nonempty
  · obtain ⟨c,hc⟩ := hc
    have hci := (mem_inter.mp hc).1
    have hcc := (mem_inter.mp hc).2
    have hs : I ⊆ cap c := by
      intro u hu
      by_cases he : u = c
      · subst u; exact mem_insert_self _ _
      · apply mem_insert_of_mem
        have huo : u ∈ outer := by
          apply mem_sdiff.mpr
          refine ⟨mem_univ _, ?_⟩
          intro huc
          exact hI hci hu (Ne.symm he) (clique_edges c hcc u huc (Ne.symm he))
        refine mem_sdiff.mpr ⟨mem_inter.mpr ⟨huo, hN hu⟩, ?_⟩
        exact hI hci hu (Ne.symm he)
    exact (card_le_card hs).trans (cap_bound c hcc (hN hci))
  · have hs : I ⊆ outer ∩ adjacency v := by
      intro u hu
      refine mem_inter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, ?_⟩, hN hu⟩
      intro huc
      exact hc ⟨u, mem_inter.mpr ⟨hu,huc⟩⟩
    exact (card_le_card hs).trans outer_bound

lemma local_indep_bound (v : Fin 105) : (witness.induce (witness.neighborSet v)).indepNum ≤ 20 := by
  classical
  obtain ⟨S,hS⟩ := (witness.induce (witness.neighborSet v)).exists_isNIndepSet_indepNum
  let I := S.map (Function.Embedding.subtype (fun w => w ∈ witness.neighborSet v))
  have hi : witness.IsIndepSet (I : Set (Fin 105)) := by
    intro a ha b hb hab hadj
    obtain ⟨a',ha',rfl⟩ := mem_map.mp ha
    obtain ⟨b',hb',rfl⟩ := mem_map.mp hb
    exact hS.isIndepSet ha' hb' (fun he => hab (congrArg Subtype.val he)) hadj
  have hn : I ⊆ adjacency v := by
    intro a ha
    obtain ⟨a',_,rfl⟩ := mem_map.mp ha
    exact a'.property
  have hc := local_selection_bound v I hi hn
  have he : I.card = S.card := card_map _
  rw [he, hS.card_eq] at hc
  exact hc

lemma max_local_bound : witness.maxLocalIndependence ≤ 20 := by
  classical
  let L := univ.image (fun v : Fin 105 => (witness.induce (witness.neighborSet v)).indepNum)
  have hall : ∀ k ∈ L, k ≤ 20 := by
    intro k hk
    obtain ⟨v,_,rfl⟩ := mem_image.mp hk
    exact local_indep_bound v
  change L.max.getD 0 ≤ 20
  cases he : L.max with
  | bot => change 0 ≤ 20; omega
  | coe k => change k ≤ 20; exact hall k (mem_of_max he)

lemma hh_complete (n : ℕ) : havelHakimiStep (List.replicate (n+2) (n+1)) = List.replicate (n+1) n := by
  rw [List.replicate_succ, havelHakimiStep]
  simp only [List.splitAt_eq, List.take_replicate, List.drop_replicate, Nat.min_self, Nat.sub_self,
    List.replicate_zero, List.append_nil, List.map_replicate, Nat.add_sub_cancel]
  apply List.eq_replicate_iff.mpr
  constructor <;> simp
lemma residue_complete (n : ℕ) : residueAux (List.replicate (n+1) n) = 1 := by
  induction n with
  | zero => rw [show List.replicate (0+1) 0 = [0] from rfl, residueAux]; rfl
  | succ n ih =>
    rw [List.replicate_succ, residueAux]
    · rw [← List.replicate_succ, hh_complete]
      exact ih
    · omega

lemma square_residue_eq : squareResidue witness = 1 := by
  classical
  have hd : ∀ v : Fin 105, witness.graphSquare.degree v = 104 := by
    intro v
    rw [← card_neighborSet_eq_degree]
    let e : witness.graphSquare.neighborSet v ≃ {w : Fin 105 // w ≠ v} :=
      Equiv.subtypeEquivRight fun w => by rw [square_complete]; simp [ne_comm]
    rw [Fintype.card_congr e]
    simp
  unfold squareResidue SimpleGraph.residue
  simp_rw [hd]
  have hs : (Multiset.map (fun _ : Fin 105 => 104) univ.val).sort (· ≥ ·) = List.replicate 105 104 := by
    apply List.eq_replicate_iff.mpr
    constructor
    · simp
    · intro k hk
      have := (Multiset.mem_sort (· ≥ ·)).mp hk
      simpa using this
  rw [hs]
  exact residue_complete 104

lemma induced_degree_bound (S : Finset (Fin 105)) : inducedMaxDegree witness S ≤ 40 := by
  classical
  let f : Copy (witness.induce (S : Set (Fin 105))) witness :=
    ⟨⟨Subtype.val, fun {_ _} h => h⟩, Subtype.val_injective⟩
  unfold inducedMaxDegree
  convert f.maxDegree_mono.trans global_degree_bound using 1
  · rfl
  · congr 1

lemma strict_every_set (S : Finset (Fin 105)) : boundOn witness S < witness.indepDominationNumber := by
  rw [boundOn, square_residue_eq, independent_domination_eq, mul_one]
  have hl := max_local_bound
  have hd := induced_degree_bound S
  omega

theorem conjecture430c_upper_M : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card W →
      G.indepDominationNumber ≤ boundOn G (maximumVertices G) := by
  intro h
  exact (not_le_of_gt (strict_every_set (maximumVertices witness)))
    (h (Fin 105) witness witness_connected (by decide))

theorem conjecture430c_upper_center : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card W →
      G.indepDominationNumber ≤ boundOn G (center G) := by
  intro h
  exact (not_le_of_gt (strict_every_set (center witness)))
    (h (Fin 105) witness witness_connected (by decide))

#print axioms conjecture430c_upper_M
#print axioms conjecture430c_upper_center
#print axioms max_local_bound
#print axioms square_residue_eq
#print axioms independent_domination_eq
end WOWII430Proof
