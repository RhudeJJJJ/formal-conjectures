import Proofs.WOWII361362.GeometryNumeric
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Tactic

open Finset SimpleGraph
namespace WOWIIGeometry
variable {V : Type*}
variable (G : SimpleGraph V)

lemma tree_path_length (hT : G.IsTree) {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q,hq,hqdist⟩ := hT.connected.exists_path_of_dist u v
  have he := (hT.isAcyclic.subsingleton_path u v).elim (⟨p,hp⟩ : G.Path u v) ⟨q,hq⟩
  have : p=q := congrArg Subtype.val he
  simpa only [this] using hqdist

lemma closer_unique (hT : G.IsTree) {w b a c : V}
    (hba : G.Adj b a) (hbc : G.Adj b c)
    (ha : G.dist w a + 1 = G.dist w b)
    (hc : G.dist w c + 1 = G.dist w b) : a=c := by
  obtain ⟨p,hp,hplen⟩ := hT.connected.exists_path_of_dist w a
  obtain ⟨q,hq,hqlen⟩ := hT.connected.exists_path_of_dist w c
  have hp' : (p.concat hba.symm).IsPath := by
    apply Walk.isPath_of_length_eq_dist
    simpa only [Walk.length_concat,hplen] using ha
  have hq' : (q.concat hbc.symm).IsPath := by
    apply Walk.isPath_of_length_eq_dist
    simpa only [Walk.length_concat,hqlen] using hc
  have he := (hT.isAcyclic.subsingleton_path w b).elim
    (⟨p.concat hba.symm,hp'⟩ : G.Path w b) ⟨q.concat hbc.symm,hq'⟩
  have he' := congrArg (fun t : G.Path w b => t.val.penultimate) he
  simpa only [Walk.penultimate_concat] using he'

lemma no_peak (hT : G.IsTree) {a b c : V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hne : a ≠ c) (w : V) :
    G.dist w b + 1 ≤ max (G.dist w a) (G.dist w c) := by
  have hl := hT.dist_eq_dist_add_one_of_adj w hab
  have hr := hT.dist_eq_dist_add_one_of_adj w hbc
  by_contra h
  have hla : G.dist w a + 1 = G.dist w b := by omega
  have hrc : G.dist w c + 1 = G.dist w b := by omega
  exact hne (closer_unique G hT hab.symm hbc hla hrc)

lemma walk_cone (hT : G.IsTree) {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (w : V) (i : ℕ) (hi : i ≤ p.length) :
    G.dist w (p.getVert i) + i ≤ G.dist w a ∨
    G.dist w (p.getVert i) + (p.length-i) ≤ G.dist w b := by
  have hn : ∀ j, j+2 ≤ p.length →
      G.dist w (p.getVert (j+1)) + 1 ≤
        max (G.dist w (p.getVert j)) (G.dist w (p.getVert (j+2))) := by
    intro j hj
    apply no_peak G hT (p.adj_getVert_succ (by omega))
      (p.adj_getVert_succ (by omega))
    intro he
    have hi' := hp.getVert_injOn (show j ≤ p.length by omega)
      (show j+2 ≤ p.length by omega) he
    omega
  simpa only [Walk.getVert_zero,Walk.getVert_length] using
    path_cone (fun j => G.dist w (p.getVert j)) p.length hn i hi

variable [Fintype V]

lemma center_dist_le (hc : G.Connected) {c : V} (hcent : c ∈ G.center) (x : V) :
    G.dist c x ≤ G.radius.toNat := by
  let _ := hc.nonempty
  have hfin := (G.radius_ne_top_iff).mpr hc
  have hh : G.edist c x ≤ G.radius := by
    rw [← hcent]
    exact G.edist_le_eccent
  exact ENat.toNat_le_toNat hh hfin

omit [Fintype V] in
lemma radius_le_of_bound (hc : G.Connected) (c : V) (k : ℕ)
    (h : ∀ x, G.dist c x ≤ k) : G.radius.toNat ≤ k := by
  have he : G.eccent c ≤ (k : ℕ∞) := by
    apply (G.eccent_le_iff c k).mpr
    intro x
    rw [← (hc c x).coe_dist_eq_edist]
    exact_mod_cast h x
  have hr := G.radius_le_eccent.trans he
  simpa using ENat.toNat_le_toNat hr (by simp)

lemma center_adj (hT : G.IsTree) {a b : V} (ha : a ∈ G.center)
    (hb : b ∈ G.center) (hne : a ≠ b) : G.Adj a b := by
  by_contra hn
  have hlong := hT.connected.one_lt_dist_of_ne_of_not_adj hne hn
  obtain ⟨p,hp,hlen⟩ := hT.connected.exists_path_of_dist a b
  let R := G.radius.toNat
  have hbound : ∀ x, G.dist (p.getVert 1) x ≤ R-1 := by
    intro x
    have hcone := walk_cone G hT p hp x 1 (by omega)
    have hax := center_dist_le G hT.connected ha x
    have hbx := center_dist_le G hT.connected hb x
    rw [G.dist_comm (u:=x) (v:=a),G.dist_comm (u:=x) (v:=b),G.dist_comm (u:=x) (v:=p.getVert 1)] at hcone
    dsimp [R]
    rcases hcone with hcone | hcone <;> omega
  have hr := radius_le_of_bound G hT.connected (p.getVert 1) (R-1) hbound
  have hpR : 0 < R := by
    have hab := center_dist_le G hT.connected ha b
    dsimp [R]
    omega
  omega

lemma center_card_le_two (hT : G.IsTree) : Nat.card G.center ≤ 2 := by
  classical
  let _ := hT.connected.nonempty
  let C : Finset V := G.center.toFinset
  obtain ⟨c,hc⟩ := G.center_nonempty
  have hcC : c ∈ C := by simpa [C] using hc
  have hone : (C.erase c).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have haC : a ∈ G.center := by simpa [C] using (mem_erase.mp ha).2
    have hbC : b ∈ G.center := by simpa [C] using (mem_erase.mp hb).2
    by_contra hne
    have hca := center_adj G hT hc haC (mem_erase.mp ha).1.symm
    have hcb := center_adj G hT hc hbC (mem_erase.mp hb).1.symm
    have hab := center_adj G hT haC hbC hne
    have hdist := hT.dist_ne_of_adj c hab
    rw [G.dist_eq_one_iff_adj.mpr hca,G.dist_eq_one_iff_adj.mpr hcb] at hdist
    exact hdist rfl
  have hcard := Finset.card_erase_add_one hcC
  have hid : Nat.card G.center = C.card := by
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  omega

lemma radius_midpoint_bound (hT : G.IsTree) :
    G.radius.toNat ≤ (G.diam+1)/2 := by
  let _ := hT.connected.nonempty
  have hfin := G.connected_iff_ediam_ne_top.mp hT.connected
  obtain ⟨a,b,hab⟩ := G.exists_dist_eq_diam
  obtain ⟨p,hp,hlen⟩ := hT.connected.exists_path_of_dist a b
  let i := p.length/2
  apply radius_le_of_bound G hT.connected (p.getVert i)
  intro x
  have hx := walk_cone G hT p hp x i (by dsimp [i]; omega)
  have ha : G.dist x a ≤ G.diam := G.dist_le_diam hfin
  have hb : G.dist x b ≤ G.diam := G.dist_le_diam hfin
  rw [G.dist_comm (u:=x) (v:=p.getVert i)] at hx
  dsimp [i] at hx
  rw [hlen,hab] at hx
  dsimp [i]
  rw [hlen,hab]
  rcases hx with hx | hx <;> omega
end WOWIIGeometry
