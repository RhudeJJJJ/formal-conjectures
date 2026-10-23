import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import Lean.Elab.Tactic.Omega

open Finset SimpleGraph
namespace WOWIICover
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma forced_support {D : Finset V} (hD : G.IsTotalDominating (D : Set V))
    {s l : V} (hl : G.degree l = 1) (hsl : G.Adj s l) : s ∈ D := by
  obtain ⟨w, hw, hlw⟩ := hD l
  obtain ⟨a, ha, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hl
  have hw' := huniq w hlw
  have hs' := huniq s hsl.symm
  have : w=s := hw'.trans hs'.symm
  simpa only [Finset.mem_coe, this] using hw

omit [DecidableRel G.Adj] in
lemma independent_component_representatives (S : Finset V) :
    ∃ R : Finset V, R ⊆ S ∧
      R.card = Nat.card (G.induce (S : Set V)).ConnectedComponent ∧
      ∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b := by
  classical
  let H := G.induce (S : Set V)
  let _ := Fintype.ofFinite H.ConnectedComponent
  let r : H.ConnectedComponent → V := fun C => C.out.val
  have hm : ∀ C : H.ConnectedComponent, H.connectedComponentMk C.out = C :=
    fun C => C.out_eq
  have hinj : Function.Injective r := by
    intro C E he
    have hv : C.out = E.out := Subtype.ext he
    rw [← hm C, ← hm E, hv]
  let R : Finset V := univ.image r
  refine ⟨R, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨C, _, rfl⟩ := mem_image.mp hv
    exact C.out.property
  · rw [show R.card = Fintype.card H.ConnectedComponent by
          simp only [R, card_image_of_injective _ hinj, card_univ]]
    exact (Nat.card_eq_fintype_card).symm
  · intro a ha b hb hab
    obtain ⟨C, _, rfl⟩ := mem_image.mp ha
    obtain ⟨E, _, rfl⟩ := mem_image.mp hb
    have hEq : C=E := by
      rw [← hm C, ← hm E]
      exact ConnectedComponent.connectedComponentMk_eq_of_adj
        (show H.Adj C.out E.out from hab)
    subst E
    exact hab.ne rfl

omit [DecidableRel G.Adj] in
lemma distance_two_cover {D S : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) (hSD : S ⊆ D) :
    ∃ F : Finset V,
      F.card + Nat.card (G.induce (S : Set V)).ConnectedComponent = D.card ∧
      ∀ v, ∃ f ∈ F, G.dist v f ≤ 2 := by
  classical
  obtain ⟨R, hRS, hcard, hR⟩ := independent_component_representatives G S
  have hRD : R ⊆ D := hRS.trans hSD
  refine ⟨D \ R, ?_, ?_⟩
  · rw [card_sdiff_of_subset hRD, ← hcard]
    exact Nat.sub_add_cancel (card_le_card hRD)
  · intro v
    obtain ⟨d, hd, hvd⟩ := hD v
    by_cases hdr : d ∈ R
    · obtain ⟨f, hf, hdf⟩ := hD d
      have hfr : f ∉ R := fun h => hR d hdr f h hdf
      refine ⟨f, mem_sdiff.mpr ⟨hf,hfr⟩, ?_⟩
      have ht := hvd.reachable.dist_triangle_left f
      rw [G.dist_eq_one_iff_adj.mpr hvd, G.dist_eq_one_iff_adj.mpr hdf] at ht
      exact ht
    · refine ⟨d, mem_sdiff.mpr ⟨hd,hdr⟩, ?_⟩
      rw [G.dist_eq_one_iff_adj.mpr hvd]
      omega
end WOWIICover

namespace WOWIICover
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma geodesic_start_dist (hc : G.Connected) {a b : V}
    (p : G.Walk a b) (hp : p.length = G.dist a b) (i : ℕ) (hi : i ≤ p.length) :
    G.dist a (p.getVert i) = i := by
  have htake := G.dist_le (p.take i)
  have hdrop := G.dist_le (p.drop i)
  rw [Walk.take_length, min_eq_left hi] at htake
  rw [Walk.drop_length] at hdrop
  have ht := hc.dist_triangle (u:=a) (v:=p.getVert i) (w:=b)
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma diameter_of_two_cover (hc : G.Connected) (F : Finset V)
    (hF : ∀ v, ∃ f ∈ F, G.dist v f ≤ 2) :
    G.diam + 1 ≤ 5 * F.card := by
  classical
  let _ := hc.nonempty
  obtain ⟨a,b,hab⟩ := G.exists_dist_eq_diam
  obtain ⟨p,hplen⟩ := hc.exists_walk_length_eq_dist a b
  let N := p.length/5+1
  have hpositions : ∀ i : Fin N, 5*i.val ≤ p.length := by
    intro i
    have hi := i.isLt
    dsimp [N] at hi
    omega
  have hex : ∀ i : Fin N, ∃ f ∈ F, G.dist (p.getVert (5*i.val)) f ≤ 2 :=
    fun i => hF (p.getVert (5*i.val))
  choose f hf hd using hex
  let ff : Fin N → F := fun i => ⟨f i,hf i⟩
  have hinj : Function.Injective ff := by
    intro i j he
    have heq : f i=f j := congrArg Subtype.val he
    have hi := geodesic_start_dist G hc p hplen (5*i.val) (hpositions i)
    have hj := geodesic_start_dist G hc p hplen (5*j.val) (hpositions j)
    have hij : G.dist (p.getVert (5*i.val)) (p.getVert (5*j.val)) ≤ 4 := by
      have htri := hc.dist_triangle (u:=p.getVert (5*i.val))
        (v:=f i) (w:=p.getVert (5*j.val))
      have hiF := hd i
      have hjF := hd j
      rw [heq] at hiF
      rw [heq, G.dist_comm (u:=f j) (v:=p.getVert (5*j.val))] at htri
      omega
    have h1 := hc.dist_triangle (u:=a) (v:=p.getVert (5*i.val))
      (w:=p.getVert (5*j.val))
    have h2 := hc.dist_triangle (u:=a) (v:=p.getVert (5*j.val))
      (w:=p.getVert (5*i.val))
    rw [hi,hj] at h1 h2
    rw [G.dist_comm (u:=p.getVert (5*j.val)) (v:=p.getVert (5*i.val))] at h2
    have hv : i.val=j.val := by omega
    exact Fin.ext hv
  have hcF : N ≤ F.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective ff hinj
  dsimp [N] at hcF
  rw [hplen,hab] at hcF
  omega

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma minimum_total_set (hc : G.Connected) (ho : 1 < Fintype.card V) :
    ∃ D : Finset V, G.IsTotalDominating (D : Set V) ∧
      D.card=G.totalDominationNumber := by
  classical
  let _ : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp ho
  have htd : G.IsTotalDominating ((univ : Finset V) : Set V) := by
    intro v
    obtain ⟨w,hw⟩ := hc.preconnected.exists_adj_of_nontrivial v
    exact ⟨w,mem_univ w,hw⟩
  have hex : {n | ∃ D : Finset V, G.IsTotalNDominatingSet n D}.Nonempty :=
    ⟨univ.card,univ,⟨htd,rfl⟩⟩
  obtain ⟨D,hD⟩ := Nat.sInf_mem hex
  exact ⟨D,hD.isTotalDominating,hD.card_eq⟩
end WOWIICover
