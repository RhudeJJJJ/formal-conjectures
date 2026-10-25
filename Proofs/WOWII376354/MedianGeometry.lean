import Proofs.WOWII361362.TreeGeometry
import Proofs.WOWII361362.GraphCover
import FormalConjectures.WrittenOnTheWallII.GraphConjecture376

/-! Transmission minimizers and the balanced edge cut in a finite tree. -/

open Finset SimpleGraph
namespace WOWIIMedian
open WrittenOnTheWallII.GraphConjecture376
variable {V : Type*} [Fintype V]
variable (T : SimpleGraph V)

lemma median_iff {v : V} : v ∈ medians T ↔ ∀ w, transmission T v ≤ transmission T w := by
  classical
  simp only [medians,mem_filter,mem_univ,true_and]

lemma transmission_no_peak (hT : T.IsTree) {a b c : V}
    (hab : T.Adj a b) (hbc : T.Adj b c) (hne : a≠c) :
    transmission T b+1 ≤ max (transmission T a) (transmission T c) := by
  have hp : ∀ w, 2*T.dist w b ≤ T.dist w a+T.dist w c := by
    intro w
    have h1 := hT.dist_eq_dist_add_one_of_adj w hab
    have h2 := hT.dist_eq_dist_add_one_of_adj w hbc
    have h3 := WOWIIGeometry.no_peak T hT hab hbc hne w
    omega
  have hstrict : ∑ w : V, 2*T.dist w b < ∑ w : V, (T.dist w a+T.dist w c) := by
    apply Finset.sum_lt_sum (fun w _ => hp w)
    refine ⟨b,mem_univ _,?_⟩
    simp only [T.dist_self,Nat.mul_zero]
    rw [T.dist_eq_one_iff_adj.mpr hab.symm,T.dist_eq_one_iff_adj.mpr hbc]
    omega
  have hleft : (∑ w : V, 2*T.dist w b)=2*transmission T b := by
    simp only [transmission,Finset.mul_sum,T.dist_comm]
  have hright : (∑ w : V, (T.dist w a+T.dist w c))=
      transmission T a+transmission T c := by
    simp only [transmission,sum_add_distrib,T.dist_comm]
  rw [hleft,hright] at hstrict
  omega

lemma medians_adj (hT : T.IsTree) {a b : V} (ha : a ∈ medians T)
    (hb : b ∈ medians T) (hne : a≠b) : T.Adj a b := by
  by_contra hn
  have hlong := hT.connected.one_lt_dist_of_ne_of_not_adj hne hn
  obtain ⟨p,hp,hlen⟩ := hT.connected.exists_path_of_dist a b
  have hc : ∀ j, j+2 ≤ p.length →
      transmission T (p.getVert (j+1))+1 ≤
        max (transmission T (p.getVert j)) (transmission T (p.getVert (j+2))) := by
    intro j hj
    apply transmission_no_peak T hT (p.adj_getVert_succ (by omega))
      (p.adj_getVert_succ (by omega))
    intro he
    have hh := hp.getVert_injOn (show j ≤ p.length by omega)
      (show j+2 ≤ p.length by omega) he
    omega
  have hcone := WOWIIGeometry.path_cone (fun j => transmission T (p.getVert j))
    p.length hc 1 (by omega)
  simp only [Walk.getVert_zero,Walk.getVert_length] at hcone
  have h1 := (median_iff T).mp ha (p.getVert 1)
  have h2 := (median_iff T).mp hb (p.getVert 1)
  rcases hcone with hcone | hcone <;> omega

lemma medians_card_le_two (hT : T.IsTree) : (medians T).card ≤ 2 := by
  classical
  by_cases he : (medians T).Nonempty
  · obtain ⟨a,ha⟩ := he
    have hone : ((medians T).erase a).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro b hb c hc
      by_contra hne
      have hab := medians_adj T hT ha (mem_erase.mp hb).2 (mem_erase.mp hb).1.symm
      have hac := medians_adj T hT ha (mem_erase.mp hc).2 (mem_erase.mp hc).1.symm
      have hbc := medians_adj T hT (mem_erase.mp hb).2 (mem_erase.mp hc).2 hne
      have hd := hT.dist_ne_of_adj a hbc
      rw [T.dist_eq_one_iff_adj.mpr hab,T.dist_eq_one_iff_adj.mpr hac] at hd
      exact hd rfl
    have hh := card_erase_add_one ha
    omega
  · simp only [not_nonempty_iff_eq_empty.mp he,card_empty]
    omega

noncomputable def side (a b : V) : Finset V := by
  classical
  exact univ.filter fun w => T.dist a w < T.dist b w

lemma side_mem {a b w : V} : w ∈ side T a b ↔ T.dist a w < T.dist b w := by
  simp only [side,mem_filter,mem_univ,true_and]

lemma side_compl [DecidableEq V] (hT : T.IsTree) {a b : V} (hab : T.Adj a b) :
    side T b a = (side T a b)ᶜ := by
  ext w
  have hn := hT.dist_ne_of_adj w hab
  rw [T.dist_comm (u:=w) (v:=a),T.dist_comm (u:=w) (v:=b)] at hn
  simp only [side_mem,mem_compl]
  omega

lemma side_step (hT : T.IsTree) {a b w : V} (hab : T.Adj a b)
    (hw : w ∈ side T a b) : T.dist b w=T.dist a w+1 := by
  have hd := hT.dist_eq_dist_add_one_of_adj w hab
  rw [T.dist_comm (u:=w) (v:=a),T.dist_comm (u:=w) (v:=b)] at hd
  have hlt := (side_mem T).mp hw
  omega

lemma side_root {a b : V} (hab : T.Adj a b) : a ∈ side T a b := by
  rw [side_mem,T.dist_self,T.dist_eq_one_iff_adj.mpr hab.symm]
  omega

lemma balanced_sides (hT : T.IsTree) {a b : V} (hab : T.Adj a b)
    (ha : a ∈ medians T) (hb : b ∈ medians T) :
    (side T a b).card=(side T b a).card := by
  classical
  have heq : transmission T a=transmission T b :=
    le_antisymm ((median_iff T).mp ha b) ((median_iff T).mp hb a)
  have hpoint : ∀ w, T.dist b w+(if w ∈ side T b a then 1 else 0)=
      T.dist a w+(if w ∈ side T a b then 1 else 0) := by
    intro w
    by_cases hw : w ∈ side T a b
    · have hnot : w ∉ side T b a := by rw [side_compl T hT hab];simpa using hw
      simp only [hw,hnot,↓reduceIte]
      exact side_step T hT hab hw
    · have hw' : w ∈ side T b a := by rw [side_compl T hT hab];simpa using hw
      simp only [hw,hw',↓reduceIte]
      exact (side_step T hT hab.symm hw').symm
  have hsum := Finset.sum_congr rfl (fun w (_ : w ∈ (univ : Finset V)) => hpoint w)
  have hcountA : (∑ w : V, if w ∈ side T a b then (1 : ℕ) else 0)=(side T a b).card := by
    simp
  have hcountB : (∑ w : V, if w ∈ side T b a then (1 : ℕ) else 0)=(side T b a).card := by
    simp
  rw [sum_add_distrib,sum_add_distrib,hcountA,hcountB] at hsum
  change transmission T b+(side T b a).card=transmission T a+(side T a b).card at hsum
  omega

lemma closer_exists (hT : T.IsTree) {r x : V} (hne : r≠x) :
    ∃ p, T.Adj x p ∧ T.dist r p+1=T.dist r x := by
  obtain ⟨p,hp,hlen⟩ := hT.connected.exists_path_of_dist r x
  have hpos : 0<p.length := by
    have hd := hT.connected.pos_dist_of_ne hne
    omega
  refine ⟨p.getVert (p.length-1),?_,?_⟩
  · have he := p.adj_getVert_succ (show p.length-1<p.length by omega)
    simpa only [Nat.sub_add_cancel (by omega : 1≤p.length),Walk.getVert_length] using he.symm
  · have hd := WOWIICover.geodesic_start_dist T hT.connected p hlen
      (p.length-1) (by omega)
    omega

lemma side_cross_edge (hT : T.IsTree) {a b x y : V} (hab : T.Adj a b)
    (hx : x ∈ side T a b) (hy : y ∈ side T b a) (hxy : T.Adj x y) : x=a ∧ y=b := by
  have hbx := side_step T hT hab hx
  have hay := side_step T hT hab.symm hy
  have h1 := hT.dist_eq_dist_add_one_of_adj a hxy
  have h2 := hT.dist_eq_dist_add_one_of_adj b hxy
  have hsame : T.dist a x=T.dist b y := by omega
  have hxa : x=a := by
    by_contra hn
    obtain ⟨p,hxp,hp⟩ := closer_exists T hT (Ne.symm hn)
    have ht := hT.connected.dist_triangle (u:=b) (v:=a) (w:=p)
    rw [T.dist_eq_one_iff_adj.mpr hab.symm] at ht
    have hbpSteps := hT.dist_eq_dist_add_one_of_adj b hxp
    have hbp : T.dist b p+1=T.dist b x := by omega
    have hby : T.dist b y+1=T.dist b x := by omega
    have he := WOWIIGeometry.closer_unique T hT hxp hxy hbp hby
    subst p
    omega
  subst x
  have hby : T.dist b y=0 := by simpa only [T.dist_self] using hsame.symm
  exact ⟨rfl,hT.connected.dist_eq_zero_iff.mp hby |>.symm⟩

end WOWIIMedian
