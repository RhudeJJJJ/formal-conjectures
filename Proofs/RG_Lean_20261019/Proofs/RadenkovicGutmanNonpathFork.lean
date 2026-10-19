/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanTreeTerminal

/-!
# Actual pendant arms in a finite nonpath tree

Choose a branching vertex farthest from a fixed root. At most one neighbor
points towards the root, so at least two point outwards. Maximal outward paths
end in leaves and have no other branching vertices. The paths are actual walks
in the given tree and meet only at their common branching root.

This is the arm-selection part of the source-presentation obligation. It does
not yet provide the labelled `CoreQuotient.source` isomorphism.
-/

namespace Gebendorfer.RadenkovicGutman.NonpathFork

open SimpleGraph TreeTerminal
open scoped Classical
noncomputable section

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem path_length_eq_dist (hT : G.IsTree) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq, hlen⟩ := hT.connected.exists_path_of_dist u v
  have he : p = q := Subtype.mk.inj (hT.isAcyclic.subsingleton_path u v |>.elim
    ⟨p, hp⟩ ⟨q, hq⟩)
  simpa only [he] using hlen

theorem dist_le_of_mem_path (hT : G.IsTree) {r v x : V}
    (p : G.Walk r v) (hp : p.IsPath) (hx : x ∈ p.support) :
    G.dist r x ≤ G.dist r v := by
  calc
    G.dist r x ≤ (p.takeUntil x hx).length := G.dist_le _
    _ ≤ p.length := p.length_takeUntil_le_length hx
    _ = G.dist r v := path_length_eq_dist hT p hp

/-- A tree has at most one neighbor closer to the chosen root. -/
theorem parent_unique (hT : G.IsTree) (r u : V) {a b : V}
    (ha : G.Adj u a) (hb : G.Adj u b)
    (hda : G.dist r a + 1 = G.dist r u)
    (hdb : G.dist r b + 1 = G.dist r u) : a = b := by
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath r a
  obtain ⟨q, hq⟩ := hT.connected.exists_isPath r b
  have hua : u ∉ p.support := by
    intro hu
    have := dist_le_of_mem_path hT p hp hu
    omega
  have hub : u ∉ q.support := by
    intro hu
    have := dist_le_of_mem_path hT q hq hu
    omega
  have he : p.concat ha.symm = q.concat hb.symm :=
    Subtype.mk.inj (hT.isAcyclic.subsingleton_path r u |>.elim
      ⟨_, hp.concat hua ha.symm⟩ ⟨_, hq.concat hub hb.symm⟩)
  exact (Walk.concat_inj he).1

/-- Two of the neighbors of any branching vertex point away from a fixed root. -/
theorem two_outward_neighbors (hT : G.IsTree) (r u : V) (hu : 3 ≤ G.degree u) :
    ∃ a b, a ≠ b ∧ G.Adj u a ∧ G.Adj u b ∧
      G.dist r a = G.dist r u + 1 ∧ G.dist r b = G.dist r u + 1 := by
  let s := G.neighborFinset u
  let out := s.filter (fun x => G.dist r u < G.dist r x)
  let inside := s.filter (fun x => ¬G.dist r u < G.dist r x)
  have hin : inside.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' : G.Adj u a ∧ ¬G.dist r u < G.dist r a := by simpa [inside, s] using ha
    have hb' : G.Adj u b ∧ ¬G.dist r u < G.dist r b := by simpa [inside, s] using hb
    apply parent_unique hT r u ha'.1 hb'.1
    · have := hT.dist_eq_dist_add_one_of_adj r ha'.1
      omega
    · have := hT.dist_eq_dist_add_one_of_adj r hb'.1
      omega
  have hsum : out.card + inside.card = G.degree u := by
    simpa only [out, inside, s, card_neighborFinset_eq_degree] using
      Finset.card_filter_add_card_filter_not (s := s) (p := fun x => G.dist r u < G.dist r x)
  have hout : 1 < out.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hout
  have ha' : G.Adj u a ∧ G.dist r u < G.dist r a := by simpa [out, s] using ha
  have hb' : G.Adj u b ∧ G.dist r u < G.dist r b := by simpa [out, s] using hb
  refine ⟨a, b, hab, ha'.1, hb'.1, ?_, ?_⟩
  · have := hT.dist_eq_dist_add_one_of_adj r ha'.1
    omega
  · have := hT.dist_eq_dist_add_one_of_adj r hb'.1
    omega

/-- Every vertex of this actual walk lies at its stated outward distance. -/
def Outward (r : V) {u v : V} (p : G.Walk u v) : Prop :=
  ∀ i, i ≤ p.length → G.dist r (p.getVert i) = G.dist r u + i

theorem outward_singleton (r : V) {u a : V} (ha : G.Adj u a)
    (hd : G.dist r a = G.dist r u + 1) :
    Outward r (Walk.cons ha Walk.nil) := by
  intro i hi
  have hi1 : i ≤ 1 := by simpa only [Walk.length_cons, Walk.length_nil] using hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl <;> simp [hd]

theorem outward_concat (r : V) {u v w : V} (p : G.Walk u v)
    (hp : Outward r p) (h : G.Adj v w)
    (hd : G.dist r w = G.dist r v + 1) : Outward r (p.concat h) := by
  intro i hi
  by_cases hil : i ≤ p.length
  · simpa only [Walk.concat_eq_append, Walk.getVert_append', if_pos hil] using hp i hil
  · have hi' : i = (p.concat h).length := by simp only [Walk.length_concat] at *; omega
    rw [hi', Walk.getVert_length, hd, hp p.length (by rfl), Walk.length_concat]
    omega

/-- There is a longest outward path with a prescribed first edge. -/
theorem maximal_outward_path (r : V) {u a : V} (ha : G.Adj u a)
    (hd : G.dist r a = G.dist r u + 1) :
    ∃ v (p : G.Walk u v), p.IsPath ∧ p.snd = a ∧ Outward r p ∧
      ∀ w (q : G.Walk u w), q.IsPath → q.snd = a → Outward r q → q.length ≤ p.length := by
  let s := {n | ∃ v (p : G.Walk u v), p.IsPath ∧ p.snd = a ∧ Outward r p ∧ p.length = n}
  have hs : s.Finite := (Set.finite_le_nat (Fintype.card V)).subset (by
    rintro n ⟨v, p, hp, _, _, rfl⟩
    exact hp.length_lt.le)
  have hne : s.Nonempty := ⟨1, a, Walk.cons ha Walk.nil, by simp [ha.ne],
    by simp, outward_singleton r ha hd, by simp⟩
  obtain ⟨k, ⟨⟨v, p, hp, hpa, hpo, hpk⟩, hmax⟩⟩ := hs.exists_maximal hne
  refine ⟨v, p, hp, hpa, hpo, ?_⟩
  intro w q hq hqa hqo
  have := hmax ⟨w, q, hq, hqa, hqo, rfl⟩
  omega

/-- A maximal outward path ends in a leaf of the original tree. -/
theorem maximal_outward_ends_leaf (hT : G.IsTree) (r : V) {u a v : V}
    (ha : G.Adj u a) (p : G.Walk u v) (hp : p.IsPath) (hpa : p.snd = a)
    (hpo : Outward r p)
    (hmax : ∀ w (q : G.Walk u w), q.IsPath → q.snd = a → Outward r q →
      q.length ≤ p.length) : G.degree v = 1 := by
  have hnil : ¬p.Nil := by
    intro hn
    have he : p.snd = u := by cases p <;> simp_all
    exact ha.ne (he.symm.trans hpa)
  have hl : 0 < p.length := Walk.not_nil_iff_lt_length.mp hnil
  have hpred := p.adj_penultimate hnil
  have hdv : G.dist r v = G.dist r u + p.length := by
    simpa only [Walk.getVert_length] using hpo p.length (by rfl)
  have hdpre : G.dist r p.penultimate + 1 = G.dist r v := by
    have := hpo (p.length - 1) (by omega)
    dsimp only [Walk.penultimate] at *
    omega
  rw [degree_eq_one_iff_existsUnique_adj]
  refine ⟨p.penultimate, hpred.symm, ?_⟩
  intro w hvw
  by_contra hne
  have hdw : G.dist r w = G.dist r v + 1 := by
    rcases hT.dist_eq_dist_add_one_of_adj r hvw with hback | hfwd
    · exact (hne (parent_unique hT r v hvw hpred.symm (by omega) hdpre)).elim
    · exact hfwd
  have hw : w ∉ p.support := by
    intro hw
    exact hne (hT.isAcyclic.eq_penultimate_of_adj_end hp hvw hw)
  have hq := hp.concat hw hvw
  have hqa : (p.concat hvw).snd = a := by
    rw [Walk.concat_eq_append, Walk.getVert_append', if_pos (by omega : 1 ≤ p.length)]
    exact hpa
  have := hmax w (p.concat hvw) hq hqa (outward_concat r p hpo hvw hdw)
  simp only [Walk.length_concat] at this
  omega

theorem paths_with_distinct_first_disjoint (hT : G.IsTree) {u v w : V}
    (p : G.Walk u v) (q : G.Walk u w) (hp : p.IsPath) (hq : q.IsPath)
    (hfirst : p.snd ≠ q.snd) {x : V} (hxp : x ∈ p.support) (hxq : x ∈ q.support) :
    x = u := by
  by_contra hxu
  have he : p.takeUntil x hxp = q.takeUntil x hxq :=
    Subtype.mk.inj (hT.isAcyclic.subsingleton_path u x |>.elim
      ⟨_, hp.takeUntil hxp⟩ ⟨_, hq.takeUntil hxq⟩)
  have := congrArg Walk.snd he
  rw [Walk.snd_takeUntil hxu, Walk.snd_takeUntil hxu] at this
  exact hfirst this

/-- The two actual positive arms selected in the original labelled tree. -/
structure PendantFork (G : SimpleGraph V) where
  root : V
  leftLeaf : V
  rightLeaf : V
  left : G.Walk root leftLeaf
  right : G.Walk root rightLeaf
  left_path : left.IsPath
  right_path : right.IsPath
  left_positive : 0 < left.length
  right_positive : 0 < right.length
  root_degree : 3 ≤ G.degree root
  left_leaf : G.degree leftLeaf = 1
  right_leaf : G.degree rightLeaf = 1
  left_unbranched : ∀ x ∈ left.support, x ≠ root → G.degree x ≤ 2
  right_unbranched : ∀ x ∈ right.support, x ≠ root → G.degree x ≤ 2
  intersection : ∀ x, x ∈ left.support → x ∈ right.support → x = root

/-- Every finite nontrivial nonpath tree has two genuine pendant arms at one branch. -/
theorem nonpath_has_pendant_fork [Nontrivial V] (hT : G.IsTree)
    (hpath : ¬Nonempty (G ≃g pathGraph (Fintype.card V))) : Nonempty (PendantFork G) := by
  have hbranch : ∃ r, 3 ≤ G.degree r := by
    by_contra h
    push_neg at h
    exact hpath (tree_path_iso_of_degree_le_two G hT (fun v => by have := h v; omega))
  obtain ⟨r, hr⟩ := hbranch
  obtain ⟨u, hu, hmax⟩ := (Finset.univ.filter (fun v => 3 ≤ G.degree v)).exists_max_image
    (fun v => G.dist r v) ⟨r, by simp [hr]⟩
  have hud : 3 ≤ G.degree u := (Finset.mem_filter.mp hu).2
  have hfar : ∀ x, G.dist r u < G.dist r x → G.degree x ≤ 2 := by
    intro x hx
    by_contra hd
    have := hmax x (by simp; omega)
    omega
  obtain ⟨a, b, hab, ha, hb, hda, hdb⟩ := two_outward_neighbors hT r u hud
  obtain ⟨v, p, hp, hpa, hpo, hpm⟩ := maximal_outward_path r ha hda
  obtain ⟨w, q, hq, hqb, hqo, hqm⟩ := maximal_outward_path r hb hdb
  have hposp : 0 < p.length := by
    have := hpm a (Walk.cons ha Walk.nil) (by simp [ha.ne]) (by simp)
      (outward_singleton r ha hda)
    simp only [Walk.length_cons, Walk.length_nil] at this
    omega
  have hposq : 0 < q.length := by
    have := hqm b (Walk.cons hb Walk.nil) (by simp [hb.ne]) (by simp)
      (outward_singleton r hb hdb)
    simp only [Walk.length_cons, Walk.length_nil] at this
    omega
  refine ⟨⟨u, v, w, p, q, hp, hq, hposp, hposq, hud,
    maximal_outward_ends_leaf hT r ha p hp hpa hpo hpm,
    maximal_outward_ends_leaf hT r hb q hq hqb hqo hqm, ?_, ?_, ?_⟩⟩
  · intro x hx hxu
    obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi; exact hxu hi.symm
    have hd := hpo i hil
    rw [hi] at hd
    exact hfar x (by omega)
  · intro x hx hxu
    obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi; exact hxu hi.symm
    have hd := hqo i hil
    rw [hi] at hd
    exact hfar x (by omega)
  · intro x hxp hxq
    exact paths_with_distinct_first_disjoint hT p q hp hq (by simpa [hpa, hqb] using hab) hxp hxq

#print axioms path_length_eq_dist
#print axioms dist_le_of_mem_path
#print axioms parent_unique
#print axioms two_outward_neighbors
#print axioms outward_singleton
#print axioms outward_concat
#print axioms maximal_outward_path
#print axioms maximal_outward_ends_leaf
#print axioms paths_with_distinct_first_disjoint
#print axioms nonpath_has_pendant_fork

end
end Gebendorfer.RadenkovicGutman.NonpathFork
