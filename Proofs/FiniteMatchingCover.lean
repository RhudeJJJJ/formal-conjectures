import FormalConjecturesUtil

/-!
# A dominating endpoint selection from a maximum matching

The elementary matching lemma recalled in Gebendorfer's WOWII 393 manuscript,
and credited there to DeLaVina--Larson--Pepper--Waller (2010).
-/
namespace FiniteMatchingCover
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

def Valid (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
    ∀ e ∈ M, ∀ f ∈ M, ∀ v, v ∈ e → v ∈ f → e = f

noncomputable def vertices (M : Finset (Sym2 V)) : Finset V :=
  M.biUnion Sym2.toFinset

omit [Fintype V] in
lemma mem_vertices {M : Finset (Sym2 V)} {v : V} :
    v ∈ vertices M ↔ ∃ e ∈ M, v ∈ e := by
  classical
  simp [vertices, Sym2.mem_toFinset]

omit [Fintype V] in
lemma insert_valid {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : Valid G M)
    {a b : V} (hab : G.Adj a b) (ha : a ∉ vertices M) (hb : b ∉ vertices M) :
    Valid G (insert s(a,b) M) := by
  classical
  refine ⟨?_, ?_⟩
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact hab
    · exact hM.1 e he
  · intro e he f hf v hve hvf
    rcases mem_insert.mp he with rfl | heOld
    · rcases mem_insert.mp hf with rfl | hfOld
      · rfl
      · rcases Sym2.mem_iff.mp hve with h | h
        · subst v; exact (ha (mem_vertices.mpr ⟨f,hfOld,hvf⟩)).elim
        · subst v; exact (hb (mem_vertices.mpr ⟨f,hfOld,hvf⟩)).elim
    · rcases mem_insert.mp hf with rfl | hfOld
      · rcases Sym2.mem_iff.mp hvf with h | h
        · subst v; exact (ha (mem_vertices.mpr ⟨e,heOld,hve⟩)).elim
        · subst v; exact (hb (mem_vertices.mpr ⟨e,heOld,hve⟩)).elim
      · exact hM.2 e heOld f hfOld v hve hvf

omit [Fintype V] in
lemma erase_valid {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : Valid G M)
    (e : Sym2 V) : Valid G (M.erase e) :=
  ⟨fun f hf => hM.1 f (mem_of_mem_erase hf),
   fun f hf g hg => hM.2 f (mem_of_mem_erase hf) g (mem_of_mem_erase hg)⟩

omit [Fintype V] in
lemma endpoint_not_mem_erase {G : SimpleGraph V} {M : Finset (Sym2 V)}
    (hM : Valid G M) {a b : V} (he : s(a,b) ∈ M) :
    a ∉ vertices (M.erase s(a,b)) := by
  rintro ha
  obtain ⟨f,hf,haf⟩ := mem_vertices.mp ha
  exact (mem_erase.mp hf).1 (hM.2 f (mem_of_mem_erase hf) _ he a haf (by simp))

omit [DecidableEq V] in
lemma exists_maximum (G : SimpleGraph V) :
    ∃ M : Finset (Sym2 V), Valid G M ∧ ∀ N, Valid G N → N.card ≤ M.card := by
  classical
  let F := univ.filter (Valid G)
  have hF : F.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_univ _, by simp [Valid]⟩⟩
  obtain ⟨M,hMF,hmax⟩ := F.exists_max_image card hF
  exact ⟨M, (mem_filter.mp hMF).2, fun N hN => hmax N (mem_filter.mpr ⟨mem_univ _,hN⟩)⟩

omit [Fintype V] in
lemma unmatched_not_adj {G : SimpleGraph V} {M : Finset (Sym2 V)}
    (hM : Valid G M) (hmax : ∀ N, Valid G N → N.card ≤ M.card)
    {a b : V} (ha : a ∉ vertices M) (hb : b ∉ vertices M) : ¬ G.Adj a b := by
  intro hab
  have he : s(a,b) ∉ M := fun h => ha (mem_vertices.mpr ⟨_,h,by simp⟩)
  have := hmax _ (insert_valid hM hab ha hb)
  rw [card_insert_of_notMem he] at this
  omega

omit [Fintype V] in
lemma no_augment_three {G : SimpleGraph V} {M : Finset (Sym2 V)}
    (hM : Valid G M) (hmax : ∀ N, Valid G N → N.card ≤ M.card)
    {a b x y : V} (he : s(a,b) ∈ M) (hx : x ∉ vertices M) (hy : y ∉ vertices M)
    (hax : G.Adj a x) (hby : G.Adj b y) : x = y := by
  classical
  by_contra hxy
  let E := M.erase s(a,b)
  have ha : a ∉ vertices E := endpoint_not_mem_erase hM he
  have hb : b ∉ vertices E := by
    simpa only [Sym2.eq_swap] using endpoint_not_mem_erase hM (a:=b) (b:=a)
      (by simpa only [Sym2.eq_swap] using he)
  have hxE : x ∉ vertices E := by
    intro h; obtain ⟨e,he',hxe⟩ := mem_vertices.mp h
    exact hx (mem_vertices.mpr ⟨e,mem_of_mem_erase he',hxe⟩)
  have hyE : y ∉ vertices E := by
    intro h; obtain ⟨e,he',hye⟩ := mem_vertices.mp h
    exact hy (mem_vertices.mpr ⟨e,mem_of_mem_erase he',hye⟩)
  have hab : a ≠ b := (hM.1 _ he).ne
  have hya : y ≠ a := fun h => hy (h ▸ mem_vertices.mpr ⟨_,he,by simp⟩)
  have hbx : b ≠ x := fun h => hx (h ▸ mem_vertices.mpr ⟨_,he,by simp⟩)
  have hbin : b ∉ vertices (insert s(a,x) E) := by
    intro h
    obtain ⟨e,he',hbe⟩ := mem_vertices.mp h
    rcases mem_insert.mp he' with rfl | he'
    · simp [Sym2.mem_iff, Ne.symm hab, hbx] at hbe
    · exact hb (mem_vertices.mpr ⟨_,he',hbe⟩)
  have hyin : y ∉ vertices (insert s(a,x) E) := by
    intro h
    obtain ⟨e,he',hye⟩ := mem_vertices.mp h
    rcases mem_insert.mp he' with rfl | he'
    · simp [Sym2.mem_iff, hya, Ne.symm hxy] at hye
    · exact hyE (mem_vertices.mpr ⟨_,he',hye⟩)
  have hvalid := insert_valid (insert_valid (erase_valid hM _) hax ha hxE) hby hbin hyin
  have h1 : s(a,x) ∉ E := fun h => hxE (mem_vertices.mpr ⟨_,h,by simp⟩)
  have h2 : s(b,y) ∉ insert s(a,x) E :=
    fun h => hyin (mem_vertices.mpr ⟨_,h,by simp⟩)
  have hc := hmax _ hvalid
  rw [card_insert_of_notMem h2, card_insert_of_notMem h1] at hc
  have hec := card_erase_of_mem he
  change (M.erase s(a,b)).card + 1 + 1 ≤ M.card at hc
  omega

/-- Choose one endpoint on each edge to dominate all nonisolated vertices. -/
lemma dominating_selection (G : SimpleGraph V) :
    ∃ M : Finset (Sym2 V), Valid G M ∧
      ∃ Q : Finset V, Q.card ≤ M.card ∧ Q ⊆ vertices M ∧
        ∀ v, (∃ w, G.Adj v w) → v ∉ Q → ∃ w ∈ Q, G.Adj v w := by
  classical
  obtain ⟨M,hM,hmax⟩ := exists_maximum G
  let pick : Sym2 V → V := fun e =>
    if ∃ z, z ∉ vertices M ∧ G.Adj e.out.1 z then e.out.1 else e.out.2
  let Q := M.image pick
  have hpick : ∀ e, pick e ∈ e := by
    intro e
    dsimp [pick]
    split_ifs
    · exact Sym2.out_fst_mem e
    · exact Sym2.out_snd_mem e
  refine ⟨M,hM,Q,card_image_le,?_,?_⟩
  · intro v hv
    obtain ⟨e,he,rfl⟩ := mem_image.mp hv
    exact mem_vertices.mpr ⟨e,he,hpick e⟩
  · intro v hv hvQ
    by_cases hvM : v ∈ vertices M
    · obtain ⟨e,he,hve⟩ := mem_vertices.mp hvM
      have hpQ : pick e ∈ Q := mem_image_of_mem pick he
      refine ⟨pick e,hpQ,?_⟩
      have hpv : v ≠ pick e := fun h => hvQ (h ▸ hpQ)
      have heout : s(e.out.1,e.out.2) = e := e.out_eq
      have hab : G.Adj e.out.1 e.out.2 := hM.1 s(e.out.1,e.out.2) (by rw [heout]; exact he)
      have hvab : v = e.out.1 ∨ v = e.out.2 := by
        rw [← heout] at hve; exact Sym2.mem_iff.mp hve
      have hpab : pick e = e.out.1 ∨ pick e = e.out.2 := by
        have hh : pick e ∈ s(e.out.1,e.out.2) := by rw [heout]; exact hpick e
        exact Sym2.mem_iff.mp hh
      rcases hvab with rfl | rfl <;> rcases hpab with hp | hp
      · exact (hpv hp.symm).elim
      · simpa [hp] using hab
      · simpa [hp] using hab.symm
      · exact (hpv hp.symm).elim
    · obtain ⟨w,hvw⟩ := hv
      have hwM : w ∈ vertices M := by
        by_contra hw
        exact unmatched_not_adj hM hmax hvM hw hvw
      obtain ⟨e,he,hwe⟩ := mem_vertices.mp hwM
      refine ⟨pick e,mem_image_of_mem pick he,?_⟩
      have heout : s(e.out.1,e.out.2) = e := e.out_eq
      have heM : s(e.out.1,e.out.2) ∈ M := by rw [heout]; exact he
      have hwab : w = e.out.1 ∨ w = e.out.2 := by
        rw [← heout] at hwe
        exact Sym2.mem_iff.mp hwe
      dsimp [pick]
      split_ifs with hex
      · obtain ⟨z,hz,haz⟩ := hex
        rcases hwab with rfl | rfl
        · exact hvw
        · have hvz : v = z := no_augment_three hM hmax (by simpa only [Sym2.eq_swap] using heM) hvM hz hvw.symm haz
          exact hvz ▸ haz.symm
      · rcases hwab with rfl | rfl
        · exact (hex ⟨v,hvM,hvw.symm⟩).elim
        · exact hvw

/-- Convert the finite edge certificate to the repository's actual matching parameter. -/
lemma card_le_matchingNumber (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) (hM : Valid G M) : (M.card : ℝ) ≤ G.matchingNumber := by
  classical
  let N : G.Subgraph := {
    verts := vertices M
    Adj := fun v w => s(v,w) ∈ M
    adj_sub := fun h => hM.1 _ h
    edge_vert := fun h => mem_vertices.mpr ⟨_,h,by simp⟩
    symm := ⟨by intro v w h; simpa only [Sym2.eq_swap] using h⟩ }
  have hN : N.IsMatching := by
    intro v hv
    obtain ⟨e,he,hve⟩ := mem_vertices.mp hv
    obtain ⟨w,rfl⟩ := Sym2.mem_iff_exists.mp hve
    refine ⟨w,he,?_⟩
    intro u hu
    exact Sym2.congr_right.mp (hM.2 _ hu _ he v (by simp) (by simp))
  have hE : N.edgeSet.toFinset = M := by
    ext e
    induction e using Sym2.ind with
    | _ a b => simp only [Set.mem_toFinset, Subgraph.mem_edgeSet]; rfl
  unfold SimpleGraph.matchingNumber
  have hfinite : {L : G.Subgraph | L.IsMatching}.Finite := Set.toFinite _
  apply le_csSup (hfinite.image (fun L => (L.edgeSet.toFinset.card : ℝ))).bddAbove
  exact ⟨N,hN,by change (N.edgeSet.toFinset.card : ℝ) = M.card; rw [hE]⟩

omit [Fintype V] [DecidableEq V] in
lemma map_valid {W : Type*} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ {a b}, G.Adj a b → H.Adj (f a) (f b))
    {M : Finset (Sym2 V)} (hM : Valid G M) :
    Valid H (M.image (Sym2.map f)) := by
  classical
  constructor
  · intro e he
    obtain ⟨e,heOld,rfl⟩ := mem_image.mp he
    induction e using Sym2.ind with
    | _ a b => exact hadj (show G.Adj a b from hM.1 s(a,b) heOld)
  · intro e he g hg v hve hvg
    obtain ⟨e,heOld,rfl⟩ := mem_image.mp he
    obtain ⟨g,hgOld,rfl⟩ := mem_image.mp hg
    rw [Sym2.mem_map] at hve hvg
    obtain ⟨a,ha,hae⟩ := hve
    obtain ⟨b,hb,hbe⟩ := hvg
    have hab := hf (hae.trans hbe.symm)
    subst b
    exact congrArg (Sym2.map f) (hM.2 _ heOld _ hgOld a ha hb)

omit [Fintype V] in
lemma vertices_map {W : Type*} [DecidableEq W] (f : V → W)
    (M : Finset (Sym2 V)) : vertices (M.image (Sym2.map f)) = (vertices M).image f := by
  classical
  ext v
  simp only [mem_vertices, mem_image]
  constructor
  · rintro ⟨e,⟨g,hg,rfl⟩,hve⟩
    rw [Sym2.mem_map] at hve
    obtain ⟨u,hu,rfl⟩ := hve
    exact ⟨u,⟨g,hg,hu⟩,rfl⟩
  · rintro ⟨u,⟨e,he,hue⟩,rfl⟩
    refine ⟨_,⟨e,he,rfl⟩,?_⟩
    rw [Sym2.mem_map]
    exact ⟨u,hue,rfl⟩

omit [Fintype V] in
lemma union_valid {G : SimpleGraph V} {M N : Finset (Sym2 V)}
    (hM : Valid G M) (hN : Valid G N) (hd : Disjoint (vertices M) (vertices N)) :
    Valid G (M ∪ N) := by
  classical
  constructor
  · intro e he
    rcases mem_union.mp he with he | he
    · exact hM.1 _ he
    · exact hN.1 _ he
  · intro e he f hf v hve hvf
    rcases mem_union.mp he with heM | heN <;> rcases mem_union.mp hf with hfM | hfN
    · exact hM.2 _ heM _ hfM v hve hvf
    · exact (Finset.disjoint_left.mp hd (mem_vertices.mpr ⟨_,heM,hve⟩)
        (mem_vertices.mpr ⟨_,hfN,hvf⟩)).elim
    · exact (Finset.disjoint_left.mp hd (mem_vertices.mpr ⟨_,hfM,hvf⟩)
        (mem_vertices.mpr ⟨_,heN,hve⟩)).elim
    · exact hN.2 _ heN _ hfN v hve hvf

omit [Fintype V] in
lemma card_le_matchingNumber_on (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (M : Finset (Sym2 V)) (hM : Valid G M) (hvR : vertices M ⊆ R) :
    (M.card : ℝ) ≤ (G.induce (R : Set V)).matchingNumber := by
  classical
  let H := G.induce (R : Set V)
  let N : Finset (Sym2 (R : Set V)) := H.edgeFinset.filter fun e => Sym2.map Subtype.val e ∈ M
  have hN : Valid H N := by
    constructor
    · intro e he; exact SimpleGraph.mem_edgeFinset.mp (mem_filter.mp he).1
    · intro e he f hf v hve hvf
      have hm := hM.2 _ (mem_filter.mp he).2 _ (mem_filter.mp hf).2 v.val
        (by rw [Sym2.mem_map]; exact ⟨v,hve,rfl⟩)
        (by rw [Sym2.mem_map]; exact ⟨v,hvf,rfl⟩)
      exact Sym2.map.injective Subtype.val_injective hm
  have hi : N.image (Sym2.map Subtype.val) = M := by
    ext e
    constructor
    · rintro he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      exact (mem_filter.mp hf).2
    · induction e using Sym2.ind with
      | _ a b =>
        intro he
        have ha : a ∈ R := hvR (mem_vertices.mpr ⟨_,he,by simp⟩)
        have hb : b ∈ R := hvR (mem_vertices.mpr ⟨_,he,by simp⟩)
        refine mem_image.mpr ⟨s(⟨a,ha⟩,⟨b,hb⟩),?_,rfl⟩
        exact mem_filter.mpr ⟨by simpa [H] using hM.1 _ he,he⟩
  have hc : N.card = M.card := by
    rw [← hi, card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  rw [← hc]
  exact card_le_matchingNumber H N hN

end FiniteMatchingCover
