import Proofs.WOWII361362.TreeGeometry
import Proofs.WOWII361362.GraphCover
import FormalConjectures.WrittenOnTheWallII.GraphConjecture354

/-! Rooted open packings with two vertices per closed-neighborhood component. -/

open Finset SimpleGraph
namespace WOWIIRootPacking
open WrittenOnTheWallII.GraphConjecture354
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (T : SimpleGraph V) [DecidableRel T.Adj]

omit [DecidableEq V] in
lemma child_exists (hT : T.IsTree) (r s : V) (hs : 2 ≤ T.degree s) :
    ∃ a, T.Adj s a ∧ T.dist r a = T.dist r s + 1 := by
  classical
  by_contra hn
  have hc : ∀ a, T.Adj s a → T.dist r a + 1 = T.dist r s := by
    intro a ha
    have hd := hT.dist_eq_dist_add_one_of_adj r ha
    have hno : T.dist r a ≠ T.dist r s + 1 := fun h => hn ⟨a,ha,h⟩
    omega
  have hsmall : (T.neighborFinset s).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact WOWIIGeometry.closer_unique T hT
      (by simpa using ha) (by simpa using hb)
      (hc a (by simpa using ha)) (hc b (by simpa using hb))
  rw [T.card_neighborFinset_eq_degree] at hsmall
  omega

lemma closed_mem_of_mem {A : Finset V} {s : V} (hs : s ∈ A) :
    s ∈ closedNeighbors T A := mem_union_left _ hs

lemma closed_mem_of_adj {A : Finset V} {s a : V} (hs : s ∈ A) (ha : T.Adj s a) :
    a ∈ closedNeighbors T A := by
  exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,s,hs,ha.symm⟩)

lemma component_A_representative (A : Finset V)
    (C : (T.induce (closedNeighbors T A : Set V)).ConnectedComponent) :
    ∃ s, ∃ hs : s ∈ A,
      (T.induce (closedNeighbors T A : Set V)).connectedComponentMk
        ⟨s,closed_mem_of_mem T hs⟩ = C := by
  classical
  have ho := C.out.property
  change C.out.val ∈ A ∪ neighbors T A at ho
  rcases mem_union.mp ho with ho | ho
  · refine ⟨C.out.val,ho,?_⟩
    exact C.out_eq
  · obtain ⟨s,hs,hcs⟩ := (mem_filter.mp ho).2
    refine ⟨s,hs,?_⟩
    rw [← C.out_eq]
    exact ConnectedComponent.connectedComponentMk_eq_of_adj
      (show (T.induce (closedNeighbors T A : Set V)).Adj
        ⟨s,closed_mem_of_mem T hs⟩ C.out from hcs.symm)

lemma packing_two_per_component (hT : T.IsTree) (A : Finset V)
    (hA : ∀ s ∈ A, 2 ≤ T.degree s) :
    ∃ P : Finset V, P.card = 2 * componentsOn T (closedNeighbors T A) ∧
      (P : Set V).Pairwise fun u v => Disjoint (T.neighborSet u) (T.neighborSet v) := by
  classical
  let r : V := Classical.choice hT.connected.nonempty
  let H := T.induce (closedNeighbors T A : Set V)
  let _ := Fintype.ofFinite H.ConnectedComponent
  have hsExists := component_A_representative T A
  choose s hs hm using hsExists
  have haExists : ∀ C : H.ConnectedComponent,
      ∃ a, T.Adj (s C) a ∧ T.dist r a = T.dist r (s C)+1 :=
    fun C => child_exists T hT r (s C) (hA _ (hs C))
  choose a ha hd using haExists
  have has : ∀ C : H.ConnectedComponent, a C ∈ closedNeighbors T A :=
    fun C => closed_mem_of_adj T (hs C) (ha C)
  have ham : ∀ C : H.ConnectedComponent, H.connectedComponentMk ⟨a C,has C⟩=C := by
    intro C
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj
      (show H.Adj ⟨a C,has C⟩ ⟨s C,closed_mem_of_mem T (hs C)⟩ from (ha C).symm)).trans
        (hm C)
  let f : H.ConnectedComponent × Bool → V := fun q => if q.2 then a q.1 else s q.1
  have hfmem : ∀ q, f q ∈ closedNeighbors T A := by
    rintro ⟨C,b⟩
    cases b <;> simp only [f,Bool.false_eq_true,↓reduceIte] <;>
      first | exact closed_mem_of_mem T (hs C) | exact has C
  have hfm : ∀ q, H.connectedComponentMk ⟨f q,hfmem q⟩ = q.1 := by
    rintro ⟨C,b⟩
    cases b <;> simp only [f,Bool.false_eq_true,↓reduceIte] <;>
      first | exact hm C | exact ham C
  have hinj : Function.Injective f := by
    rintro ⟨C,b⟩ ⟨E,d⟩ he
    have hec : C=E := by
      exact (hfm (C,b)).symm.trans
        ((congrArg H.connectedComponentMk (Subtype.ext he)).trans (hfm (E,d)))
    subst E
    have heb : b=d := by
      cases b <;> cases d <;> simp_all [f, (ha C).ne, (ha C).ne.symm]
    subst d
    rfl
  let P := univ.image f
  refine ⟨P,?_,?_⟩
  · rw [show P.card=Fintype.card (H.ConnectedComponent × Bool) by
          simp only [P,card_image_of_injective _ hinj,card_univ]]
    simp only [Fintype.card_prod,Fintype.card_bool]
    change Fintype.card H.ConnectedComponent*2=2*Nat.card H.ConnectedComponent
    rw [Nat.card_eq_fintype_card]
    exact Nat.mul_comm _ _
  · intro u hu v hv hne
    obtain ⟨⟨C,b⟩,_,rfl⟩ := mem_image.mp hu
    obtain ⟨⟨E,d⟩,_,rfl⟩ := mem_image.mp hv
    apply Set.disjoint_left.mpr
    intro z huz hvz
    change T.Adj (f (C,b)) z at huz
    change T.Adj (f (E,d)) z at hvz
    by_cases hec : C=E
    · subst E
      have hbd : b≠d := by intro h; subst d; exact hne rfl
      have hdist := hT.dist_ne_of_adj z (ha C)
      cases b <;> cases d <;> simp only [f,Bool.false_eq_true,↓reduceIte] at *
      all_goals first
        | exact hbd rfl
        | exact hdist (by rw [T.dist_eq_one_iff_adj.mpr huz.symm,
            T.dist_eq_one_iff_adj.mpr hvz.symm])
    · have hzoutside : z ∉ closedNeighbors T A := by
        intro hz
        apply hec
        have he := (ConnectedComponent.connectedComponentMk_eq_of_adj
          (show H.Adj ⟨f (C,b),hfmem _⟩ ⟨z,hz⟩ from huz)).trans
          (ConnectedComponent.connectedComponentMk_eq_of_adj
            (show H.Adj ⟨z,hz⟩ ⟨f (E,d),hfmem _⟩ from hvz.symm))
        exact (hfm (C,b)).symm.trans (he.trans (hfm (E,d)))
      have hb : b=true := by
        cases b
        · exact False.elim (hzoutside (closed_mem_of_adj T (hs C) huz))
        · rfl
      have hdd : d=true := by
        cases d
        · exact False.elim (hzoutside (closed_mem_of_adj T (hs E) hvz))
        · rfl
      subst b
      subst d
      simp only [f,↓reduceIte] at huz hvz hne
      have hdz : ∀ Q : H.ConnectedComponent, T.Adj (a Q) z →
          T.dist r (a Q)+1=T.dist r z := by
        intro Q hQ
        have hneq : s Q ≠ z := by
          intro he
          exact hzoutside (he ▸ closed_mem_of_mem T (hs Q))
        have hsteps := hT.dist_eq_dist_add_one_of_adj r hQ
        by_contra hno
        have hzcloser : T.dist r z+1=T.dist r (a Q) := by omega
        have hsame := WOWIIGeometry.closer_unique T hT (ha Q).symm hQ
          (hd Q).symm hzcloser
        exact hneq hsame
      exact hne (WOWIIGeometry.closer_unique T hT huz.symm hvz.symm
        (hdz C huz) (hdz E hvz))

end WOWIIRootPacking
