import Proofs.TDAUniform

/-! Weighted deletion identities for indexed hypergraphs of edge sizes one to three. -/

namespace TotalDominationAnnihilationProof.Hypergraph
open Finset

variable {V I : Type*} [DecidableEq V]

def edgeWeight (k : ℕ) : ℕ := if k = 1 then 4 else if k = 2 then 2 else 1

@[simp] theorem edgeWeight_one : edgeWeight 1 = 4 := by decide
@[simp] theorem edgeWeight_two : edgeWeight 2 = 2 := by decide
@[simp] theorem edgeWeight_three : edgeWeight 3 = 1 := by decide

theorem edgeWeight_pos (k : ℕ) : 1 ≤ edgeWeight k := by
  unfold edgeWeight
  split_ifs <;> omega

def potential (U : Finset V) (J : Finset I) (edge : I → Finset V) : ℕ :=
  2 * U.card + ∑ i ∈ J, edgeWeight (edge i).card

def incidentWeight (J : Finset I) (edge : I → Finset V) (v : V) : ℕ :=
  ∑ i ∈ incident J edge v, edgeWeight (edge i).card

theorem incidentWeight_eq_card (J : Finset I) (edge : I → Finset V)
    (hthree : ∀ i ∈ J, (edge i).card = 3) (v : V) :
    incidentWeight J edge v = (incident J edge v).card := by
  unfold incidentWeight
  rw [Finset.sum_const_nat (m := 1)]
  · omega
  · intro i hi
    rw [hthree i (mem_incident.mp hi).1]
    exact edgeWeight_three

theorem weight_le_incidentWeight (J : Finset I) (edge : I → Finset V)
    {i : I} {v : V} (hi : i ∈ J) (hv : v ∈ edge i) :
    edgeWeight (edge i).card ≤ incidentWeight J edge v := by
  classical
  have hmem : i ∈ incident J edge v := mem_incident.mpr ⟨hi, hv⟩
  have heq := sum_erase_add (incident J edge v) (fun j => edgeWeight (edge j).card) hmem
  unfold incidentWeight
  omega

/-- A vertex of weighted incidence at most three that meets a two-edge
has at most two incident edges altogether. -/
theorem incident_card_le_two_of_two_edge (J : Finset I) (edge : I → Finset V)
    {i : I} {v : V} (hi : i ∈ J) (hv : v ∈ edge i)
    (hsize : (edge i).card = 2) (hlow : incidentWeight J edge v ≤ 3) :
    (incident J edge v).card ≤ 2 := by
  classical
  have himem : i ∈ incident J edge v := mem_incident.mpr ⟨hi, hv⟩
  have heq := sum_erase_add (incident J edge v) (fun j => edgeWeight (edge j).card) himem
  rw [hsize, edgeWeight_two] at heq
  have hbound : ((incident J edge v).erase i).card ≤
      ∑ j ∈ (incident J edge v).erase i, edgeWeight (edge j).card := by
    calc
      _ = ∑ _j ∈ (incident J edge v).erase i, (1 : ℕ) := by simp
      _ ≤ _ := sum_le_sum fun j _ => edgeWeight_pos (edge j).card
  have hcard := card_erase_of_mem himem
  change (∑ j ∈ incident J edge v, edgeWeight (edge j).card) ≤ 3 at hlow
  omega

/-- Any other edge at such a vertex has size three. -/
theorem other_edge_is_three (J : Finset I) (edge : I → Finset V)
    {i j : I} {v : V} (hi : i ∈ J) (hj : j ∈ J)
    (hv : v ∈ edge i) (hvj : v ∈ edge j) (hij : i ≠ j)
    (hsize : (edge i).card = 2) (hsizej : 1 ≤ (edge j).card ∧ (edge j).card ≤ 3)
    (hlow : incidentWeight J edge v ≤ 3) : (edge j).card = 3 := by
  classical
  have himem : i ∈ incident J edge v := mem_incident.mpr ⟨hi, hv⟩
  have hjmem : j ∈ (incident J edge v).erase i :=
    mem_erase.mpr ⟨Ne.symm hij, mem_incident.mpr ⟨hj, hvj⟩⟩
  have heq := sum_erase_add (incident J edge v) (fun k => edgeWeight (edge k).card) himem
  rw [hsize, edgeWeight_two] at heq
  have hsmall := sum_erase_add ((incident J edge v).erase i)
    (fun k => edgeWeight (edge k).card) hjmem
  have hwj : edgeWeight (edge j).card ≤ 1 := by
    change (∑ k ∈ incident J edge v, edgeWeight (edge k).card) ≤ 3 at hlow
    omega
  unfold edgeWeight at hwj
  split_ifs at hwj <;> omega

open scoped Classical in
/-- Strong vertex deletion removes its two vertex units and every incident edge weight. -/
theorem potential_strong_delete (U : Finset V) (J : Finset I) (edge : I → Finset V)
    {v : V} (hv : v ∈ U) :
    potential (U.erase v) (J \ incident J edge v) edge + 2 +
      incidentWeight J edge v = potential U J edge := by
  classical
  have hsub : incident J edge v ⊆ J := by
    intro i hi
    exact (mem_incident.mp hi).1
  have hsum := sum_sdiff hsub (f := fun i => edgeWeight (edge i).card)
  have hcard := card_erase_of_mem hv
  have hpos : 0 < U.card := card_pos.mpr ⟨v, hv⟩
  unfold potential incidentWeight
  omega

open scoped Classical in
/-- Deleting a second vertex which lies in no retained edge costs two units. -/
theorem potential_erase_isolated (U : Finset V) (J : Finset I) (edge : I → Finset V)
    {v : V} (hv : v ∈ U) :
    potential (U.erase v) J edge + 2 = potential U J edge := by
  have hcard := card_erase_of_mem hv
  have hpos : 0 < U.card := card_pos.mpr ⟨v, hv⟩
  unfold potential
  omega

open scoped Classical in
/-- Shrinking three-edges at a vertex increases their total weight by its incidence count. -/
theorem sum_weight_erase (J : Finset I) (edge : I → Finset V) (v : V)
    (hthree : ∀ i ∈ J, v ∈ edge i → (edge i).card = 3) :
    (∑ i ∈ J, edgeWeight ((edge i).erase v).card) =
      (∑ i ∈ J, edgeWeight (edge i).card) + (incident J edge v).card := by
  have hpoint : ∀ i ∈ J, edgeWeight ((edge i).erase v).card =
      edgeWeight (edge i).card + if v ∈ edge i then 1 else 0 := by
    intro i hi
    by_cases hv : v ∈ edge i
    · rw [card_erase_of_mem hv, hthree i hi hv]
      simp [hv]
    · rw [erase_eq_of_notMem hv]
      simp [hv]
  rw [sum_congr rfl hpoint, sum_add_distrib]
  congr 1
  simp only [incident, card_eq_sum_ones, sum_filter]

open scoped Classical in
/-- A vertex meeting a two-edge can be in at most one retained row after deleting
all rows through the other endpoint. -/
theorem residual_incident_le_one (J : Finset I) (edge : I → Finset V)
    {i : I} {u v : V} (hi : i ∈ J) (hui : u ∈ edge i) (hvi : v ∈ edge i)
    (hdeg : (incident J edge v).card ≤ 2) :
    (incident (J \ incident J edge u) edge v).card ≤ 1 := by
  have hsub : incident (J \ incident J edge u) edge v ⊆ (incident J edge v).erase i := by
    intro j hj
    obtain ⟨hjK, hvj⟩ := mem_incident.mp hj
    obtain ⟨hjJ, hju⟩ := mem_sdiff.mp hjK
    refine mem_erase.mpr ⟨?_, mem_incident.mpr ⟨hjJ, hvj⟩⟩
    intro hji
    subst j
    exact hju (mem_incident.mpr ⟨hi, hui⟩)
  have hc := card_le_card hsub
  have he := card_erase_of_mem (mem_incident.mpr ⟨hi, hvi⟩)
  omega

/-- A two-edge exhausts a weighted-incidence budget of two. -/
theorem two_edge_only (J : Finset I) (edge : I → Finset V)
    {i j : I} {v : V} (hi : i ∈ J) (hj : j ∈ J)
    (hvi : v ∈ edge i) (hvj : v ∈ edge j) (hsize : (edge i).card = 2)
    (hlow : incidentWeight J edge v ≤ 2) : j = i := by
  classical
  by_contra hne
  have hi' := mem_incident.mpr ⟨hi, hvi⟩
  have hj' := mem_erase.mpr ⟨hne, mem_incident.mpr ⟨hj, hvj⟩⟩
  have hs := sum_erase_add (incident J edge v) (fun k => edgeWeight (edge k).card) hi'
  rw [hsize, edgeWeight_two] at hs
  have ht := sum_erase_add ((incident J edge v).erase i)
    (fun k => edgeWeight (edge k).card) hj'
  have hp := edgeWeight_pos (edge j).card
  unfold incidentWeight at hlow
  omega

/-- Orient a two-edge towards the endpoint with greater weighted incidence. -/
theorem orient_two_edge (J : Finset I) (edge : I → Finset V) {i : I}
    (hsize : (edge i).card = 2) :
    ∃ u v : V, u ≠ v ∧ edge i = {u, v} ∧
      incidentWeight J edge v ≤ incidentWeight J edge u := by
  classical
  obtain ⟨a, b, hab, heq⟩ := card_eq_two.mp hsize
  by_cases hle : incidentWeight J edge b ≤ incidentWeight J edge a
  · exact ⟨a, b, hab, heq, hle⟩
  · exact ⟨b, a, hab.symm, heq.trans (pair_comm a b), by omega⟩

open scoped Classical in
/-- Delete both endpoints of an oriented two-edge, remove rows through the
chosen endpoint, and shrink the at most one remaining row through the other. -/
theorem two_edge_potential_drop (U : Finset V) (J : Finset I) (edge : I → Finset V)
    {i : I} {u v : V} (hi : i ∈ J) (hu : u ∈ U) (hv : v ∈ U) (huv : u ≠ v)
    (hui : u ∈ edge i) (hvi : v ∈ edge i) (hsize : (edge i).card = 2)
    (hdeg : (incident J edge v).card ≤ 2)
    (horient : incidentWeight J edge v ≤ incidentWeight J edge u)
    (hthree : ∀ j ∈ J \ incident J edge u, v ∈ edge j → (edge j).card = 3) :
    potential ((U.erase u).erase v) (J \ incident J edge u)
      (fun j => (edge j).erase v) + 6 ≤ potential U J edge := by
  classical
  let K := J \ incident J edge u
  have hstrong := potential_strong_delete U J edge hu
  have hv' : v ∈ U.erase u := mem_erase.mpr ⟨huv.symm, hv⟩
  have hiso := potential_erase_isolated (U.erase u) K edge hv'
  have hsum := sum_weight_erase K edge v hthree
  have hchange : potential ((U.erase u).erase v) K (fun j => (edge j).erase v) =
      potential ((U.erase u).erase v) K edge + (incident K edge v).card := by
    unfold potential
    omega
  have hr := residual_incident_le_one J edge hi hui hvi hdeg
  have hw := weight_le_incidentWeight J edge hi hui
  rw [hsize, edgeWeight_two] at hw
  by_cases hhigh : 3 ≤ incidentWeight J edge u
  · change (incident K edge v).card ≤ 1 at hr
    change potential (U.erase u) K edge + 2 + incidentWeight J edge u =
      potential U J edge at hstrong
    omega
  · have hlowv : incidentWeight J edge v ≤ 2 := by omega
    have hzero : incident K edge v = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨hjK, hvj⟩ := mem_incident.mp hj
      obtain ⟨hjJ, hju⟩ := mem_sdiff.mp hjK
      have hji := two_edge_only J edge hi hjJ hvi hvj hsize hlowv
      subst j
      exact hju (mem_incident.mpr ⟨hi, hui⟩)
    have hzc : (incident K edge v).card = 0 := by rw [hzero]; rfl
    change potential (U.erase u) K edge + 2 + incidentWeight J edge u =
      potential U J edge at hstrong
    omega

end TotalDominationAnnihilationProof.Hypergraph

#print axioms TotalDominationAnnihilationProof.Hypergraph.sum_weight_erase
#print axioms TotalDominationAnnihilationProof.Hypergraph.two_edge_potential_drop
