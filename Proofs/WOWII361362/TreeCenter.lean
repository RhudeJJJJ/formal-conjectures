import Proofs.WOWII361362.TreeGeometry
import Mathlib.Tactic

open Finset SimpleGraph
namespace WOWIIGeometry
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma third_vertex (ho : 2 < Fintype.card V) (a b : V) :
    ∃ x, x ≠ a ∧ x ≠ b := by
  classical
  by_contra h
  have hs : (univ : Finset V) ⊆ {a,b} := by
    intro x _
    by_cases ha : x=a
    · simp [ha]
    have hb : x=b := by
      by_contra hb
      exact h ⟨x,ha,hb⟩
    simp [hb]
  have hcard := card_le_card hs
  have htwo : ({a,b} : Finset V).card ≤ 2 := by
    simpa only [card_singleton] using card_insert_le a ({b} : Finset V)
  rw [card_univ] at hcard
  omega

omit [DecidableEq V] in
lemma leaf_distance (hc : G.Connected) {l c x : V} (hl : G.degree l=1)
    (hlc : G.Adj l c) (hx : x ≠ l) :
    G.dist c x + 1 = G.dist l x := by
  obtain ⟨q,hq⟩ := hc.exists_walk_length_eq_dist l x
  cases q with
  | nil => exact (hx rfl).elim
  | @cons l v x hlv p =>
    obtain ⟨a,ha,huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hl
    have he : v=c := (huniq v hlv).trans (huniq c hlc).symm
    subst v
    have ht := G.dist_le p
    have htri := hc.dist_triangle (u:=l) (v:=c) (w:=x)
    rw [G.dist_eq_one_iff_adj.mpr hlc] at htri
    simp only [Walk.length_cons] at hq
    omega

lemma center_not_leaf (hT : G.IsTree) (ho : 2 < Fintype.card V)
    {c : V} (hc : c ∈ G.center) : G.degree c ≠ 1 := by
  intro hd
  obtain ⟨w,hw,huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hd
  let R := G.radius.toNat
  by_cases hsmall : R ≤ 1
  · obtain ⟨x,hxc,hxw⟩ := third_vertex (V:=V) ho c w
    have hbound := center_dist_le G hT.connected hc x
    have hpos := hT.connected.pos_dist_of_ne hxc.symm
    have hone : G.dist c x=1 := by dsimp [R] at hsmall; omega
    exact hxw (huniq x (G.dist_eq_one_iff_adj.mp hone))
  have hb : ∀ x, G.dist w x ≤ R-1 := by
    intro x
    by_cases hx : x=c
    · subst x
      rw [G.dist_eq_one_iff_adj.mpr hw.symm]
      omega
    have hdist := leaf_distance G hT.connected hd hw hx
    have hcB := center_dist_le G hT.connected hc x
    dsimp [R]
    omega
  have hr := radius_le_of_bound G hT.connected w (R-1) hb
  omega

omit [DecidableRel G.Adj] in
lemma center_card_small_radius (hT : G.IsTree) (ho : 2 < Fintype.card V)
    (hr : G.radius.toNat ≤ 1) : Nat.card G.center ≤ 1 := by
  classical
  let C : Finset V := G.center.toFinset
  have hcard : C.card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    have ha' : a ∈ G.center := by simpa [C] using ha
    have hb' : b ∈ G.center := by simpa [C] using hb
    by_contra hne
    obtain ⟨x,hxa,hxb⟩ := third_vertex (V:=V) ho a b
    have hax := center_dist_le G hT.connected ha' x
    have hbx := center_dist_le G hT.connected hb' x
    have hpa := hT.connected.pos_dist_of_ne hxa.symm
    have hpb := hT.connected.pos_dist_of_ne hxb.symm
    have hda : G.dist a x=1 := by omega
    have hdb : G.dist b x=1 := by omega
    have hab := center_adj G hT ha' hb' hne
    have hbad := hT.dist_ne_of_adj x hab
    rw [G.dist_comm (u:=x) (v:=a),G.dist_comm (u:=x) (v:=b),hda,hdb] at hbad
    exact hbad rfl
  have hid : Nat.card G.center=C.card := by
    rw [Nat.card_eq_fintype_card,← Set.toFinset_card]
  omega

lemma other_neighbor {u v : V} (huv : G.Adj u v) (hu : G.degree u ≠ 1) :
    ∃ w, G.Adj u w ∧ w ≠ v := by
  by_contra h
  have hone : G.degree u=1 := degree_eq_one_iff_existsUnique_adj.mpr
    ⟨v,huv,fun w hw => by
      by_contra hn
      exact h ⟨w,hw,hn⟩⟩
  exact hu hone

lemma center_card_of_depth_two (hT : G.IsTree) (ho : 2 < Fintype.card V)
    (z : V) (hz : ∀ t, G.Adj z t → G.degree t ≠ 1)
    (hdepth : ∀ v, G.dist z v ≤ 2) : Nat.card G.center ≤ 1 := by
  classical
  have hR := radius_le_of_bound G hT.connected z 2 hdepth
  by_cases hsmall : G.radius.toNat ≤ 1
  · exact center_card_small_radius G hT ho hsmall
  have hr : G.radius.toNat=2 := by omega
  let _ := hT.connected.nonempty
  have hfin := (G.radius_ne_top_iff).mpr hT.connected
  have hrad : G.radius=(2 : ℕ∞) := by
    rw [← ENat.natCast_toNat hfin,hr]
    norm_num
  have hzcent : z ∈ G.center := by
    change G.eccent z=G.radius
    apply le_antisymm ?_ G.radius_le_eccent
    rw [hrad]
    apply (G.eccent_le_iff z 2).mpr
    intro x
    rw [← (hT.connected z x).coe_dist_eq_edist]
    exact_mod_cast hdepth x
  have honly : ∀ c, c ∈ G.center → c=z := by
    intro c hc
    by_contra hcz
    have hzc := center_adj G hT hzcent hc (Ne.symm hcz)
    obtain ⟨t,hzt,htc⟩ := other_neighbor G hzc (center_not_leaf G hT ho hzcent)
    obtain ⟨x,htx,hxz⟩ := other_neighbor G hzt.symm (hz t hzt)
    have hxc : x ≠ c := by
      intro he
      subst x
      have hbad := hT.dist_ne_of_adj z htx
      rw [G.dist_eq_one_iff_adj.mpr hzt,G.dist_eq_one_iff_adj.mpr hzc] at hbad
      exact hbad rfl
    let p : G.Walk c x := .cons hzc.symm (.cons hzt (.cons htx .nil))
    have hp : p.IsPath := by
      have htz := hzt.ne.symm
      have hxt := htx.ne.symm
      simp_all [p,Walk.cons_isPath_iff]
      exact ⟨⟨htx.ne,hzt.ne,Ne.symm hxz⟩,Ne.symm htc,Ne.symm hxc⟩
    have hlen := tree_path_length G hT p hp
    have hlen3 : p.length=3 := rfl
    rw [hlen3] at hlen
    have hbound := center_dist_le G hT.connected hc x
    omega
  have hcard : G.center.toFinset.card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    exact (honly a (by simpa using ha)).trans (honly b (by simpa using hb)).symm
  rw [Nat.card_eq_fintype_card,← Set.toFinset_card]
  exact hcard
end WOWIIGeometry
