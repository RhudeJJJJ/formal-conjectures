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

end TotalDominationAnnihilationProof.Hypergraph
