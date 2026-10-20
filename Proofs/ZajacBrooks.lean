/-
Brooks' theorem, following Zając, formalized by Nick Winter's erdos-617-r5 project.
Source: nwinter/erdos-617-r5 @ 32f1bfe6759299ef3a1c6e8b4c3c637528a9881b,
lean617/Lean617/R6/Brooks.lean. Mathematical proof: Mariusz Zając,
arXiv:1805.11176. Adaptation to Lean 4.33.1 and extraction of the generic theorem
for the present bridge: Jonas J. Gebendorfer / Codex, 14 October 2026.
The extracted namespace is renamed to avoid colliding with the full r=6 import. No attribution of the original proof or its
formalization to the adapting author is intended.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.unusedSectionVars false

open Finset List

open scoped Classical

namespace Gebendorfer.Zajac

namespace Brooks

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

/-! ## Partial colourings and the greedy engine -/

/-- A partial proper colouring: adjacent coloured vertices get distinct colours. -/
def PProper (H : SimpleGraph V) (c : V → Option (Fin k)) : Prop :=
  ∀ ⦃u w : V⦄, H.Adj u w → ∀ a : Fin k, c u = some a → c w ≠ some a

variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- If the blocked set (colours on neighbours) has fewer than `k` elements,
some colour of `Fin k` is free at `v`. -/
lemma exists_free_colour (c : V → Option (Fin k)) (v : V)
    (hb : (((H.neighborFinset v).image c).erase none).card < k) :
    ∃ a : Fin k, ∀ w ∈ H.neighborFinset v, c w ≠ some a := by
  by_contra hcon
  push Not at hcon
  have hsub : Finset.univ.image (fun a : Fin k => (some a : Option (Fin k)))
      ⊆ ((H.neighborFinset v).image c).erase none := by
    intro b hb'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hb'
    obtain ⟨a, rfl⟩ := hb'
    obtain ⟨w, hw, hcw⟩ := hcon a
    exact Finset.mem_erase.mpr ⟨by simp, Finset.mem_image.mpr ⟨w, hw, hcw⟩⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h),
    Finset.card_univ, Fintype.card_fin] at hle
  omega

/-- The blocked set never exceeds the degree. -/
lemma blocked_le_degree (c : V → Option (Fin k)) (v : V) :
    (((H.neighborFinset v).image c).erase none).card ≤ H.degree v :=
  le_trans (Finset.card_le_card (Finset.erase_subset _ _))
    (le_trans Finset.card_image_le
      (le_of_eq (SimpleGraph.card_neighborFinset_eq_degree H v)))

/-- An uncoloured neighbour buys one unit of slack: the blocked set stays
below `k`. -/
lemma blocked_lt_of_uncoloured_nbr (c : V → Option (Fin k)) {v w : V}
    (hw : w ∈ H.neighborFinset v) (hcw : c w = none) (hdeg : H.degree v ≤ k) :
    (((H.neighborFinset v).image c).erase none).card < k := by
  have hsub : ((H.neighborFinset v).image c).erase none
      ⊆ ((H.neighborFinset v).erase w).image c := by
    intro b hb
    obtain ⟨hbne, hbmem⟩ := Finset.mem_erase.mp hb
    obtain ⟨x, hx, hcx⟩ := Finset.mem_image.mp hbmem
    have hxw : x ≠ w := by
      intro h
      rw [h, hcw] at hcx
      exact hbne hcx.symm
    exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxw, hx⟩, hcx⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_erase_of_mem hw, SimpleGraph.card_neighborFinset_eq_degree] at h1
  have hd1 : 1 ≤ H.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨w, hw⟩
  omega

/-- Two same-coloured neighbours buy one unit of slack: the blocked set stays
below `k`. -/
lemma blocked_lt_of_collision (c : V → Option (Fin k)) {v x y : V}
    (hx : x ∈ H.neighborFinset v) (hy : y ∈ H.neighborFinset v) (hxy : x ≠ y)
    (hcxy : c x = c y) (hdeg : H.degree v ≤ k) :
    (((H.neighborFinset v).image c).erase none).card < k := by
  have hsub : ((H.neighborFinset v).image c).erase none
      ⊆ ((H.neighborFinset v).erase x).image c := by
    intro b hb
    obtain ⟨hbne, hbmem⟩ := Finset.mem_erase.mp hb
    obtain ⟨z, hz, hcz⟩ := Finset.mem_image.mp hbmem
    by_cases hzx : z = x
    · subst hzx
      exact Finset.mem_image.mpr ⟨y, Finset.mem_erase.mpr ⟨hxy.symm, hy⟩, hcxy ▸ hcz⟩
    · exact Finset.mem_image.mpr ⟨z, Finset.mem_erase.mpr ⟨hzx, hz⟩, hcz⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_erase_of_mem hx, SimpleGraph.card_neighborFinset_eq_degree] at h1
  have hd1 : 1 ≤ H.degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨x, hx⟩
  omega

/-- Extending a partial proper colouring at a vertex with a colour free on its
neighbourhood keeps it proper. -/
lemma PProper.extend {c : V → Option (Fin k)} (hp : PProper H c) {v : V}
    {a : Fin k} (ha : ∀ w ∈ H.neighborFinset v, c w ≠ some a) :
    PProper H (Function.update c v (some a)) := by
  intro u w huw b hub
  rw [Function.update_apply] at hub ⊢
  by_cases huv : u = v
  · rw [if_pos huv] at hub
    have hwv : w ≠ v := fun h => H.ne_of_adj (h ▸ huv ▸ huw) rfl
    rw [if_neg hwv]
    obtain rfl : a = b := by simpa using hub
    exact ha w ((SimpleGraph.mem_neighborFinset H v w).mpr (huv ▸ huw))
  · rw [if_neg huv] at hub
    by_cases hwv : w = v
    · rw [if_pos hwv]
      intro hab
      obtain rfl : a = b := by simpa using hab
      exact ha u ((SimpleGraph.mem_neighborFinset H v u).mpr (hwv ▸ huw).symm) hub
    · rw [if_neg hwv]
      exact hp huw b hub

/-- A total proper partial colouring is a colouring. -/
lemma colorable_of_total (c : V → Option (Fin k)) (hp : PProper H c)
    (htot : ∀ z, c z ≠ none) : H.Colorable k := by
  have hex : ∀ z, ∃ a, c z = some a := fun z => Option.ne_none_iff_exists'.mp (htot z)
  choose f hf using hex
  refine ⟨SimpleGraph.Coloring.mk f ?_⟩
  intro u w huw heq
  exact hp huw (f u) (hf u) (by rw [heq]; exact hf w)

/-- **PathColor** (Zając): greedily colour every vertex of `l` along the chain
`l ++ [z]` of uncoloured vertices; each vertex is coloured while its successor
is still uncoloured, so at most `k − 1` colours are blocked. The final vertex
`z` — and everything outside `l` — is left untouched. -/
lemma pathColor (hdeg : ∀ z : V, H.degree z ≤ k) :
    ∀ (l : List V) (z : V) (c : V → Option (Fin k)), PProper H c →
      List.IsChain H.Adj (l ++ [z]) → (l ++ [z]).Nodup →
      (∀ w ∈ l ++ [z], c w = none) →
      ∃ c' : V → Option (Fin k), PProper H c' ∧
        (∀ w, w ∉ l → c' w = c w) ∧ (∀ w ∈ l, c' w ≠ none) := by
  intro l
  induction l with
  | nil =>
    intro z c hp _ _ _
    exact ⟨c, hp, fun w _ => rfl, fun w hw => absurd hw (List.not_mem_nil)⟩
  | cons w rest ih =>
    intro z c hp hch hnd hunc
    have hne : rest ++ [z] ≠ [] := by simp
    obtain ⟨s, t, hst⟩ := List.exists_cons_of_ne_nil hne
    have hsmem : s ∈ rest ++ [z] := by rw [hst]; exact List.mem_cons_self
    have hadj : H.Adj w s := by
      have hch' : List.IsChain H.Adj (w :: (rest ++ [z])) := hch
      rw [hst] at hch'
      exact (List.isChain_cons_cons.mp hch').1
    have hwnot : w ∉ rest ++ [z] := (List.nodup_cons.mp hnd).1
    have hs_unc : c s = none := hunc s (List.mem_cons_of_mem _ hsmem)
    obtain ⟨a, ha⟩ := exists_free_colour H c w
      (blocked_lt_of_uncoloured_nbr H c ((SimpleGraph.mem_neighborFinset H w s).mpr hadj)
        hs_unc (hdeg w))
    have hp₁ : PProper H (Function.update c w (some a)) := hp.extend H ha
    have hunc' : ∀ x ∈ rest ++ [z], Function.update c w (some a) x = none := by
      intro x hx
      have hxw : x ≠ w := by
        intro h
        exact hwnot (h ▸ hx)
      rw [Function.update_apply, if_neg hxw]
      exact hunc x (List.mem_cons_of_mem _ hx)
    obtain ⟨c', hp', hkeep, hcol⟩ := ih z (Function.update c w (some a)) hp₁
      hch.tail (List.nodup_cons.mp hnd).2 hunc'
    refine ⟨c', hp', ?_, ?_⟩
    · intro x hx
      have hxw : x ≠ w := fun h => hx (h ▸ List.mem_cons_self)
      have hxrest : x ∉ rest := fun h => hx (List.mem_cons_of_mem _ h)
      rw [hkeep x hxrest, Function.update_apply, if_neg hxw]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · have hxrest : x ∉ rest := fun h => hwnot (List.mem_append_left _ h)
        rw [hkeep x hxrest, Function.update_apply, if_pos rfl]
        simp
      · exact hcol x hx'

/-! ## Maximal paths and list splitting -/

/-- Splitting a list at its first element satisfying `p` (classical). -/
lemma exists_first_split {p : V → Prop} :
    ∀ {l : List V}, (∃ x ∈ l, p x) →
      ∃ t w r, l = t ++ w :: r ∧ p w ∧ ∀ u ∈ t, ¬p u := by
  intro l
  induction l with
  | nil =>
    rintro ⟨x, hx, -⟩
    exact absurd hx (List.not_mem_nil)
  | cons a l ih =>
    intro hex
    by_cases hpa : p a
    · exact ⟨[], a, l, rfl, hpa, by simp⟩
    · have hex' : ∃ x ∈ l, p x := by
        obtain ⟨x, hx, hpx⟩ := hex
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact absurd hpx hpa
        · exact ⟨x, hx', hpx⟩
      obtain ⟨t, w, r, rfl, hpw, ht⟩ := ih hex'
      refine ⟨a :: t, w, r, rfl, hpw, ?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact hpa
      · exact ht u hu'

/-- Fuel recursion for `exists_maximal_path`. -/
lemma exists_maximal_path_aux :
    ∀ (fuel : ℕ) (l₀ : List V), Fintype.card V ≤ fuel + l₀.length → l₀ ≠ [] →
      l₀.Nodup → List.IsChain H.Adj l₀ →
      ∃ L : List V, l₀ <+: L ∧ ∃ hL : L ≠ [], L.Nodup ∧ List.IsChain H.Adj L ∧
        ∀ w, H.Adj (L.getLast hL) w → w ∈ L := by
  intro fuel
  induction fuel with
  | zero =>
    intro l₀ hcard hne hnd hch
    refine ⟨l₀, List.prefix_refl _, hne, hnd, hch, ?_⟩
    intro w _
    by_contra hwnot
    have hdisj : ∀ a ∈ l₀, ∀ b ∈ [w], a ≠ b := by
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      intro h
      exact hwnot (h ▸ ha)
    have hnd' : (l₀ ++ [w]).Nodup := by
      rw [List.nodup_append]
      exact ⟨hnd, List.nodup_singleton w, hdisj⟩
    have := hnd'.length_le_card
    simp only [List.length_append, List.length_singleton] at this
    omega
  | succ fuel ih =>
    intro l₀ hcard hne hnd hch
    by_cases hmax : ∀ w, H.Adj (l₀.getLast hne) w → w ∈ l₀
    · exact ⟨l₀, List.prefix_refl _, hne, hnd, hch, hmax⟩
    · push Not at hmax
      obtain ⟨w, hadj, hwnot⟩ := hmax
      have hdisj : ∀ a ∈ l₀, ∀ b ∈ [w], a ≠ b := by
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        intro h
        exact hwnot (h ▸ ha)
      have hnd' : (l₀ ++ [w]).Nodup := by
        rw [List.nodup_append]
        exact ⟨hnd, List.nodup_singleton w, hdisj⟩
      have hch' : List.IsChain H.Adj (l₀ ++ [w]) := by
        refine hch.append (List.isChain_singleton w) ?_
        intro x hx y hy
        rw [List.getLast?_eq_some_getLast hne, Option.mem_some_iff] at hx
        simp only [List.head?_cons, Option.mem_some_iff] at hy
        rw [← hx, ← hy]
        exact hadj
      obtain ⟨L, hpre, hLne, hLnd, hLch, hLmax⟩ := ih (l₀ ++ [w])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp) hnd' hch'
      exact ⟨L, (List.prefix_append _ _).trans hpre, hLne, hLnd, hLch, hLmax⟩

/-- **Maximal path**: any nonempty chain extends to one whose last vertex has
all its neighbours on the path. -/
lemma exists_maximal_path (l₀ : List V) (hne : l₀ ≠ []) (hnd : l₀.Nodup)
    (hch : List.IsChain H.Adj l₀) :
    ∃ L : List V, l₀ <+: L ∧ ∃ hL : L ≠ [], L.Nodup ∧ List.IsChain H.Adj L ∧
      ∀ w, H.Adj (L.getLast hL) w → w ∈ L :=
  exists_maximal_path_aux H (Fintype.card V) l₀ (Nat.le_add_right _ _) hne hnd hch

/-! ## Induced-subgraph transport (`comap` onto `Finset` subtypes) -/

/-- The partial colouring on `V` induced by a colouring of the subtype graph:
coloured exactly on `S`. -/
def partialOf (S : Finset V) (f : ↥S → Fin k) : V → Option (Fin k) :=
  fun u => if h : u ∈ S then some (f ⟨u, h⟩) else none

lemma partialOf_eq_none_iff {S : Finset V} {f : ↥S → Fin k} {z : V} :
    partialOf S f z = none ↔ z ∉ S := by
  unfold partialOf
  by_cases h : z ∈ S
  · simp [h]
  · simp [h]

lemma partialOf_pproper (S : Finset V)
    (f : (H.comap (Subtype.val : ↥S → V)).Coloring (Fin k)) :
    PProper H (partialOf S (fun a => f a)) := by
  intro u w huw a hu
  unfold partialOf at hu ⊢
  by_cases hus : u ∈ S
  · rw [dif_pos hus] at hu
    by_cases hws : w ∈ S
    · rw [dif_pos hws]
      intro hw
      have hval : f ⟨u, hus⟩ ≠ f ⟨w, hws⟩ := f.valid huw
      exact hval (Option.some.inj (hu.trans hw.symm))
    · rw [dif_neg hws]
      simp
  · rw [dif_neg hus] at hu
    exact absurd hu (by simp)

/-- The induced subgraph's degrees are dominated by the ambient degrees. -/
lemma degree_comap_le (S : Finset V) (a : ↥S) :
    (H.comap (Subtype.val : ↥S → V)).degree a ≤ H.degree a.val := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro b hb
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hb ⊢
    exact hb
  · exact fun b _ b' _ h => Subtype.val_injective h

/-- Clique-freeness passes to induced subgraphs. -/
lemma cliqueFree_comap {m : ℕ} (S : Finset V) (hcf : H.CliqueFree m) :
    (H.comap (Subtype.val : ↥S → V)).CliqueFree m := by
  intro T hT
  apply hcf (T.image Subtype.val)
  rw [SimpleGraph.isNClique_iff] at hT ⊢
  obtain ⟨hclique, hcardT⟩ := hT
  rw [SimpleGraph.isClique_iff] at hclique ⊢
  constructor
  · intro a ha b hb hab
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hne : a' ≠ b' := fun h => hab (h ▸ rfl)
    exact hclique ha' hb' hne
  · rw [Finset.card_image_of_injective _ Subtype.val_injective, hcardT]

/-- Colouring two halves with no cross edges colours the whole graph. -/
lemma colorable_of_no_cross (S : Finset V)
    (hcross : ∀ u w, H.Adj u w → u ∈ S → w ∈ S)
    (h1 : (H.comap (Subtype.val : ↥S → V)).Colorable k)
    (h2 : (H.comap (Subtype.val : ↥(Sᶜ) → V)).Colorable k) :
    H.Colorable k := by
  obtain ⟨f₁⟩ := h1
  obtain ⟨f₂⟩ := h2
  refine ⟨SimpleGraph.Coloring.mk
    (fun z => if h : z ∈ S then f₁ ⟨z, h⟩ else f₂ ⟨z, Finset.mem_compl.mpr h⟩) ?_⟩
  intro u w huw
  by_cases hu : u ∈ S <;> by_cases hw : w ∈ S
  · simp only [dif_pos hu, dif_pos hw]
    exact f₁.valid huw
  · exact absurd (hcross u w huw hu) hw
  · exact absurd (hcross w u huw.symm hw) hu
  · simp only [dif_neg hu, dif_neg hw]
    exact f₂.valid huw

/-! ## Structure lemmas -/

/-- In a `K_{k+1}`-free graph, a vertex of full degree `k` has two non-adjacent
neighbours (else its closed neighbourhood is a `K_{k+1}`). -/
lemma exists_nonadj_of_cliqueFree {v : V} (hcf : H.CliqueFree (k + 1))
    (hdegv : H.degree v = k) :
    ∃ x ∈ H.neighborFinset v, ∃ y ∈ H.neighborFinset v, ¬H.Adj x y ∧ x ≠ y := by
  by_contra hcon
  push Not at hcon
  apply hcf (insert v (H.neighborFinset v))
  rw [SimpleGraph.isNClique_iff]
  constructor
  · rw [SimpleGraph.isClique_iff]
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact (SimpleGraph.mem_neighborFinset H a b).mp hb
    · exact ((SimpleGraph.mem_neighborFinset H b a).mp ha).symm
    · by_contra hnadj
      exact hab (hcon a ha b hb hnadj)
  · have hvnot : v ∉ H.neighborFinset v := by
      intro h
      exact H.irrefl ((SimpleGraph.mem_neighborFinset H v v).mp h)
    rw [Finset.card_insert_of_notMem hvnot,
      SimpleGraph.card_neighborFinset_eq_degree, hdegv]

/-! ## The three colouring finishes -/

/-- **Delete-and-extend**: a proper partial colouring missing exactly one
vertex of degree `< k` extends to a full colouring. -/
lemma colorable_of_delete_extend {v₀ : V} (hd : H.degree v₀ < k)
    (c₀ : V → Option (Fin k)) (hp₀ : PProper H c₀)
    (hsupp : ∀ z, c₀ z = none ↔ z = v₀) : H.Colorable k := by
  have hb : (((H.neighborFinset v₀).image c₀).erase none).card < k :=
    lt_of_le_of_lt (blocked_le_degree H c₀ v₀) hd
  obtain ⟨a, ha⟩ := exists_free_colour H c₀ v₀ hb
  apply colorable_of_total H (Function.update c₀ v₀ (some a)) (hp₀.extend H ha)
  intro z
  rw [Function.update_apply]
  by_cases hz : z = v₀
  · rw [if_pos hz]
    simp
  · rw [if_neg hz]
    exact fun h => hz ((hsupp z).mp h)

/-- **Case 1 of Zając's regular case**: the maximal path spans all of `V`.
The path is `x :: v :: y :: (M₁ ++ w₀ :: M₂)` with `x, y` non-adjacent
neighbours of `v` and `w₀` a third neighbour of `v`. Colour `x, y` alike,
greedy along `M₁` (successor `w₀`), then down from the far end (successor `v`),
and colour `v` last off the `x, y` collision. -/
lemma colorable_of_spanning_path (hk : 3 ≤ k) (hdeg : ∀ z : V, H.degree z ≤ k)
    {x v y w₀ : V} {M₁ M₂ : List V}
    (hxy : ¬H.Adj x y) (hxv : H.Adj v x) (hyv : H.Adj v y) (hw₀ : H.Adj v w₀)
    (hLnd : (x :: v :: y :: (M₁ ++ w₀ :: M₂)).Nodup)
    (hLch : List.IsChain H.Adj (x :: v :: y :: (M₁ ++ w₀ :: M₂)))
    (hAll : ∀ u : V, u ∈ x :: v :: y :: (M₁ ++ w₀ :: M₂)) :
    H.Colorable k := by
  have hk0 : 0 < k := by omega
  -- nodup dissection
  obtain ⟨hxnot, hnd1⟩ := List.nodup_cons.mp hLnd
  obtain ⟨hvnot, hnd2⟩ := List.nodup_cons.mp hnd1
  obtain ⟨hynot, hndM⟩ := List.nodup_cons.mp hnd2
  obtain ⟨hxv', hxy', hxM₁, hxw₀, hxM₂⟩ :
      x ≠ v ∧ x ≠ y ∧ x ∉ M₁ ∧ x ≠ w₀ ∧ x ∉ M₂ := by
    simpa [List.mem_cons, List.mem_append, not_or] using hxnot
  obtain ⟨hvy', hvM₁, hvw₀, hvM₂⟩ : v ≠ y ∧ v ∉ M₁ ∧ v ≠ w₀ ∧ v ∉ M₂ := by
    simpa [List.mem_cons, List.mem_append, not_or] using hvnot
  obtain ⟨hyM₁, hyw₀, hyM₂⟩ : y ∉ M₁ ∧ y ≠ w₀ ∧ y ∉ M₂ := by
    simpa [List.mem_append, List.mem_cons, not_or] using hynot
  obtain ⟨hndM₁, hndw, hdisj⟩ := List.nodup_append.mp hndM
  obtain ⟨hw₀M₂, hndM₂⟩ := List.nodup_cons.mp hndw
  have hw₀M₁ : w₀ ∉ M₁ := fun h => hdisj w₀ h w₀ List.mem_cons_self rfl
  have hM₁M₂ : ∀ a ∈ M₁, a ∉ M₂ :=
    fun a ha hb => hdisj a ha a (List.mem_cons_of_mem _ hb) rfl
  -- chain dissection
  have hchM : List.IsChain H.Adj (M₁ ++ w₀ :: M₂) := hLch.tail.tail.tail
  -- initial colouring: x and y get colour 0
  set c₀ : V → Option (Fin k) :=
    Function.update (Function.update (fun _ => (none : Option (Fin k))) x
      (some ⟨0, hk0⟩)) y (some ⟨0, hk0⟩) with hc₀def
  have hc₀val : ∀ z, z ≠ x → z ≠ y → c₀ z = none := by
    intro z hzx hzy
    rw [hc₀def, Function.update_apply, if_neg hzy, Function.update_apply, if_neg hzx]
  have hc₀x : c₀ x = some ⟨0, hk0⟩ := by
    rw [hc₀def, Function.update_apply, if_neg hxy', Function.update_apply, if_pos rfl]
  have hc₀y : c₀ y = some ⟨0, hk0⟩ := by
    rw [hc₀def, Function.update_apply, if_pos rfl]
  have hp₀ : PProper H c₀ := by
    have hbase : PProper H (fun _ => (none : Option (Fin k))) := by
      intro u w huw a hu
      exact absurd hu (by simp)
    have hstep : PProper H (Function.update (fun _ => (none : Option (Fin k))) x
        (some ⟨0, hk0⟩)) := by
      apply hbase.extend H
      intro w _
      simp
    rw [hc₀def]
    apply hstep.extend H
    intro w hw
    rw [Function.update_apply]
    by_cases hwx : w = x
    · subst hwx
      exact absurd ((SimpleGraph.mem_neighborFinset H y w).mp hw).symm hxy
    · rw [if_neg hwx]
      simp
  -- PathColor 1: along M₁, successor w₀
  have hchain₁ : List.IsChain H.Adj (M₁ ++ [w₀]) :=
    hchM.prefix ⟨M₂, by simp⟩
  have hnd₁ : (M₁ ++ [w₀]).Nodup :=
    hndM.sublist (List.Sublist.append_left
      (List.Sublist.cons_cons w₀ (List.nil_sublist M₂)) M₁)
  have hunc₁ : ∀ z ∈ M₁ ++ [w₀], c₀ z = none := by
    intro z hz
    rcases List.mem_append.mp hz with h | h
    · exact hc₀val z (fun he => hxM₁ (he ▸ h)) (fun he => hyM₁ (he ▸ h))
    · rw [List.mem_singleton] at h
      subst h
      exact hc₀val z (fun he => hxw₀ he.symm) (fun he => hyw₀ he.symm)
  obtain ⟨c₁, hp₁, hkeep₁, hcol₁⟩ := pathColor H hdeg M₁ w₀ c₀ hp₀ hchain₁ hnd₁ hunc₁
  -- PathColor 2: down from the far end, (w₀ :: M₂).reverse, successor v
  have hchW : List.IsChain H.Adj (w₀ :: M₂) := hchM.suffix ⟨M₁, rfl⟩
  have hchain₂ : List.IsChain H.Adj ((w₀ :: M₂).reverse ++ [v]) := by
    apply List.IsChain.append
    · exact List.isChain_reverse.mpr (hchW.imp fun a b h => h.symm)
    · exact List.isChain_singleton v
    · intro p hp q hq
      rw [List.getLast?_reverse, List.head?_cons, Option.mem_some_iff] at hp
      rw [List.head?_cons, Option.mem_some_iff] at hq
      rw [← hp, ← hq]
      exact hw₀.symm
  have hnd₂ : ((w₀ :: M₂).reverse ++ [v]).Nodup := by
    rw [List.nodup_append]
    refine ⟨List.nodup_reverse.mpr hndw, List.nodup_singleton v, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    rw [List.mem_reverse] at ha
    rcases List.mem_cons.mp ha with rfl | h
    · exact fun he => hvw₀ he.symm
    · exact fun he => hvM₂ (he ▸ h)
  have hunc₂ : ∀ z ∈ (w₀ :: M₂).reverse ++ [v], c₁ z = none := by
    intro z hz
    have hzcases : z ∈ w₀ :: M₂ ∨ z = v := by
      rcases List.mem_append.mp hz with h | h
      · exact Or.inl (List.mem_reverse.mp h)
      · exact Or.inr (List.mem_singleton.mp h)
    have hzM₁ : z ∉ M₁ := by
      rcases hzcases with h | rfl
      · rcases List.mem_cons.mp h with rfl | h'
        · exact hw₀M₁
        · exact fun hin => hM₁M₂ z hin h'
      · exact hvM₁
    rw [hkeep₁ z hzM₁]
    rcases hzcases with h | rfl
    · rcases List.mem_cons.mp h with rfl | h'
      · exact hc₀val z (fun he => hxw₀ he.symm) (fun he => hyw₀ he.symm)
      · exact hc₀val z (fun he => hxM₂ (he ▸ h')) (fun he => hyM₂ (he ▸ h'))
    · exact hc₀val z (fun he => hxv' he.symm) (fun he => hvy' he)
  obtain ⟨c₂, hp₂, hkeep₂, hcol₂⟩ :=
    pathColor H hdeg ((w₀ :: M₂).reverse) v c₁ hp₁ hchain₂ hnd₂ hunc₂
  -- the collision finish at v
  have hxW : x ∉ (w₀ :: M₂).reverse := by
    rw [List.mem_reverse]
    intro h
    rcases List.mem_cons.mp h with h' | h'
    · exact hxw₀ h'
    · exact hxM₂ h'
  have hyW : y ∉ (w₀ :: M₂).reverse := by
    rw [List.mem_reverse]
    intro h
    rcases List.mem_cons.mp h with h' | h'
    · exact hyw₀ h'
    · exact hyM₂ h'
  have hc₂x : c₂ x = some ⟨0, hk0⟩ := by
    rw [hkeep₂ x hxW, hkeep₁ x hxM₁, hc₀x]
  have hc₂y : c₂ y = some ⟨0, hk0⟩ := by
    rw [hkeep₂ y hyW, hkeep₁ y hyM₁, hc₀y]
  have hblocked := blocked_lt_of_collision H c₂
    ((SimpleGraph.mem_neighborFinset H v x).mpr hxv)
    ((SimpleGraph.mem_neighborFinset H v y).mpr hyv)
    hxy' (hc₂x.trans hc₂y.symm) (hdeg v)
  obtain ⟨a, ha⟩ := exists_free_colour H c₂ v hblocked
  apply colorable_of_total H (Function.update c₂ v (some a)) (hp₂.extend H ha)
  intro z
  rw [Function.update_apply]
  by_cases hzv : z = v
  · rw [if_pos hzv]
    simp
  · rw [if_neg hzv]
    have hzL := hAll z
    simp only [List.mem_cons, List.mem_append] at hzL
    rcases hzL with rfl | rfl | rfl | h | rfl | h
    · rw [hc₂x]
      simp
    · exact absurd rfl hzv
    · rw [hc₂y]
      simp
    · -- z ∈ M₁
      have hzW : z ∉ (w₀ :: M₂).reverse := by
        rw [List.mem_reverse]
        intro hin
        rcases List.mem_cons.mp hin with rfl | h'
        · exact hw₀M₁ h
        · exact hM₁M₂ z h h'
      rw [hkeep₂ z hzW]
      exact hcol₁ z h
    · exact hcol₂ z (by rw [List.mem_reverse]; exact List.mem_cons_self)
    · exact hcol₂ z (by rw [List.mem_reverse]; exact List.mem_cons_of_mem _ h)

/-- **Case 2b of Zając's regular case**: the cycle patch. The cycle is
`D = D₁ ++ vl :: vl1 :: D₂'` (as a path, closed by the edge from its last
vertex to its head); `vl` is the last cycle vertex with an outside neighbour
`u₀`; `vl1`, its successor, has all its neighbours inside the cycle. Given a
proper partial colouring `c₀` whose support is exactly the complement of the
cycle, colour `vl1` with `u₀`'s colour, greedy around the cycle ending before
`vl`, and colour `vl` last off the `u₀, vl1` collision. -/
lemma colorable_of_cycle_patch (hdeg : ∀ z : V, H.degree z ≤ k)
    {D₁ D₂' : List V} {vl vl1 u₀ : V}
    (hDnd : (D₁ ++ vl :: vl1 :: D₂').Nodup)
    (hDch : List.IsChain H.Adj (D₁ ++ vl :: vl1 :: D₂'))
    (hclose : ∀ e ∈ (D₁ ++ vl :: vl1 :: D₂').getLast?,
      ∀ hd ∈ (D₁ ++ vl :: vl1 :: D₂').head?, H.Adj e hd)
    (hu₀ : u₀ ∉ D₁ ++ vl :: vl1 :: D₂') (hadju : H.Adj vl u₀)
    (hins : ∀ w, H.Adj vl1 w → w ∈ D₁ ++ vl :: vl1 :: D₂')
    (c₀ : V → Option (Fin k)) (hp₀ : PProper H c₀)
    (hsupp : ∀ z, c₀ z = none ↔ z ∈ D₁ ++ vl :: vl1 :: D₂') :
    H.Colorable k := by
  -- nodup dissection
  obtain ⟨hndD₁, hndtail, hdisj⟩ := List.nodup_append.mp hDnd
  obtain ⟨hvlnot, hndtail'⟩ := List.nodup_cons.mp hndtail
  obtain ⟨hvl1not, hndD₂'⟩ := List.nodup_cons.mp hndtail'
  have hvlvl1 : vl ≠ vl1 := fun h => hvlnot (h ▸ List.mem_cons_self)
  have hvlD₂' : vl ∉ D₂' := fun h => hvlnot (List.mem_cons_of_mem _ h)
  have hvl1D₁ : vl1 ∉ D₁ :=
    fun h => hdisj vl1 h vl1 (List.mem_cons_of_mem _ List.mem_cons_self) rfl
  have hvlD₁ : vl ∉ D₁ := fun h => hdisj vl h vl List.mem_cons_self rfl
  -- adjacency vl ∼ vl1 (consecutive on the cycle)
  have hadj_vl : H.Adj vl vl1 :=
    (List.isChain_cons_cons.mp (hDch.suffix ⟨D₁, rfl⟩)).1
  -- u₀ facts and its colour
  have hvl1mem : vl1 ∈ D₁ ++ vl :: vl1 :: D₂' :=
    List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hu₀vl1 : u₀ ≠ vl1 := fun h => hu₀ (h ▸ hvl1mem)
  have hc₀u₀ : c₀ u₀ ≠ none := fun h => hu₀ ((hsupp u₀).mp h)
  obtain ⟨a₀, ha₀⟩ := Option.ne_none_iff_exists'.mp hc₀u₀
  -- colour vl1 with u₀'s colour (all of vl1's neighbours are uncoloured)
  have hnbr_unc : ∀ w ∈ H.neighborFinset vl1, c₀ w ≠ some a₀ := by
    intro w hw
    have hwD : w ∈ D₁ ++ vl :: vl1 :: D₂' :=
      hins w ((SimpleGraph.mem_neighborFinset H vl1 w).mp hw)
    rw [(hsupp w).mpr hwD]
    simp
  have hp₁ : PProper H (Function.update c₀ vl1 (some a₀)) := hp₀.extend H hnbr_unc
  -- PathColor around the cycle: D₂' ++ D₁, successor vl
  have hchain : List.IsChain H.Adj ((D₂' ++ D₁) ++ [vl]) := by
    rw [List.append_assoc]
    apply List.IsChain.append
    · exact hDch.suffix ⟨D₁ ++ [vl, vl1], by simp⟩
    · exact hDch.prefix ⟨vl1 :: D₂', by simp⟩
    · intro p hp q hq
      have hpD : (D₁ ++ vl :: vl1 :: D₂').getLast? = some p := by
        have hD₂'last : D₂'.getLast? = some p := hp
        have hshape : D₁ ++ vl :: vl1 :: D₂' = (D₁ ++ [vl, vl1]) ++ D₂' := by simp
        rw [hshape, List.getLast?_append, hD₂'last, Option.some_or]
      have hqD : (D₁ ++ vl :: vl1 :: D₂').head? = some q := by
        have hq' : (D₁ ++ [vl]).head? = some q := hq
        rw [List.head?_append] at hq' ⊢
        rw [List.head?_cons] at hq' ⊢
        exact hq'
      exact hclose p hpD q hqD
  have hndW : ((D₂' ++ D₁) ++ [vl]).Nodup := by
    have hsub : D₁ ++ vl :: D₂' <+ D₁ ++ vl :: vl1 :: D₂' :=
      List.Sublist.append_left
        (List.Sublist.cons_cons vl (List.sublist_cons_self vl1 D₂')) D₁
    have hnd_sub : (D₁ ++ vl :: D₂').Nodup := hDnd.sublist hsub
    have hperm : (D₁ ++ vl :: D₂').Perm ((D₂' ++ D₁) ++ [vl]) := by
      have hshape : D₁ ++ vl :: D₂' = (D₁ ++ [vl]) ++ D₂' := by simp
      have hshape' : (D₂' ++ D₁) ++ [vl] = D₂' ++ (D₁ ++ [vl]) := by simp
      rw [hshape, hshape']
      exact List.perm_append_comm
    exact hperm.nodup hnd_sub
  have huncW : ∀ z ∈ (D₂' ++ D₁) ++ [vl], Function.update c₀ vl1 (some a₀) z = none := by
    intro z hz
    have hzmem : z ∈ D₁ ++ vl :: vl1 :: D₂' ∧ z ≠ vl1 := by
      rcases List.mem_append.mp hz with h | h
      · rcases List.mem_append.mp h with h' | h'
        · exact ⟨List.mem_append_right _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')),
            fun he => hvl1not (he ▸ h')⟩
        · exact ⟨List.mem_append_left _ h', fun he => hvl1D₁ (he ▸ h')⟩
      · rw [List.mem_singleton] at h
        subst h
        exact ⟨List.mem_append_right _ List.mem_cons_self, hvlvl1⟩
    rw [Function.update_apply, if_neg hzmem.2]
    exact (hsupp z).mpr hzmem.1
  obtain ⟨c₂, hp₂, hkeep₂, hcol₂⟩ := pathColor H hdeg (D₂' ++ D₁) vl
    (Function.update c₀ vl1 (some a₀)) hp₁ hchain hndW huncW
  -- the collision finish at vl
  have hu₀W : u₀ ∉ D₂' ++ D₁ := by
    intro h
    rcases List.mem_append.mp h with h' | h'
    · exact hu₀ (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')))
    · exact hu₀ (List.mem_append_left _ h')
  have hvl1W : vl1 ∉ D₂' ++ D₁ := by
    intro h
    rcases List.mem_append.mp h with h' | h'
    · exact hvl1not (h' : vl1 ∈ D₂')
    · exact hvl1D₁ h'
  have hc₂u₀ : c₂ u₀ = some a₀ := by
    rw [hkeep₂ u₀ hu₀W, Function.update_apply, if_neg hu₀vl1, ha₀]
  have hc₂vl1 : c₂ vl1 = some a₀ := by
    rw [hkeep₂ vl1 hvl1W, Function.update_apply, if_pos rfl]
  have hblocked := blocked_lt_of_collision H c₂
    ((SimpleGraph.mem_neighborFinset H vl u₀).mpr hadju)
    ((SimpleGraph.mem_neighborFinset H vl vl1).mpr hadj_vl)
    hu₀vl1 (hc₂u₀.trans hc₂vl1.symm) (hdeg vl)
  obtain ⟨a, ha⟩ := exists_free_colour H c₂ vl hblocked
  apply colorable_of_total H (Function.update c₂ vl (some a)) (hp₂.extend H ha)
  intro z
  rw [Function.update_apply]
  by_cases hzvl : z = vl
  · rw [if_pos hzvl]
    simp
  · rw [if_neg hzvl]
    by_cases hzD : z ∈ D₁ ++ vl :: vl1 :: D₂'
    · rcases List.mem_append.mp hzD with h | h
      · exact hcol₂ z (List.mem_append_right _ h)
      · rcases List.mem_cons.mp h with rfl | h'
        · exact absurd rfl hzvl
        · rcases List.mem_cons.mp h' with rfl | h''
          · rw [hc₂vl1]
            simp
          · exact hcol₂ z (List.mem_append_left _ h'')
    · -- outside the cycle: still carries the inductive colouring
      have hzW : z ∉ D₂' ++ D₁ := by
        intro h
        rcases List.mem_append.mp h with h' | h'
        · exact hzD (List.mem_append_right _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')))
        · exact hzD (List.mem_append_left _ h')
      have hzvl1 : z ≠ vl1 := fun he => hzD (he ▸ hvl1mem)
      rw [hkeep₂ z hzW, Function.update_apply, if_neg hzvl1]
      exact fun h => hzD ((hsupp z).mp h)

end Brooks

/-! ## The main induction (Zając's proof of Brooks' theorem) -/

open Brooks in
/-- **Brooks' theorem in Zając's exception-free form** (arXiv:1805.11176),
strong-induction core: for `k ≥ 3`, every graph on at most `n` vertices with
`Δ ≤ k` and no `K_{k+1}` is `k`-colourable. -/
theorem brooks_strong (k : ℕ) (hk : 3 ≤ k) :
    ∀ (n : ℕ) {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
      [DecidableRel H.Adj], Fintype.card V ≤ n → (∀ z, H.degree z ≤ k) →
      H.CliqueFree (k + 1) → H.Colorable k := by
  intro n
  induction n with
  | zero =>
    intro V _ _ H _ hcard _ _
    exact (H.colorable_of_fintype).mono (le_trans hcard (Nat.zero_le _))
  | succ n IH =>
    intro V instF instD H instR hcard hdeg hcf
    by_cases hsmall : Fintype.card V ≤ k
    · exact (H.colorable_of_fintype).mono hsmall
    push Not at hsmall
    by_cases hlow : ∃ z, H.degree z < k
    · -- a vertex of degree < k: delete it, colour by induction, extend greedily
      obtain ⟨v₀, hv₀⟩ := hlow
      have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v₀⟩
      have hcardS : Fintype.card ↥(Finset.univ.erase v₀) ≤ n := by
        rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ v₀),
          Finset.card_univ]
        omega
      obtain ⟨f⟩ := IH (H.comap (Subtype.val : ↥(Finset.univ.erase v₀) → V)) hcardS
        (fun a => le_trans (degree_comap_le H _ a) (hdeg a.val))
        (Brooks.cliqueFree_comap H _ hcf)
      apply colorable_of_delete_extend H hv₀
        (partialOf (Finset.univ.erase v₀) (fun a => f a))
        (partialOf_pproper H _ f)
      intro z
      rw [partialOf_eq_none_iff]
      simp [Finset.mem_erase]
    · -- H is k-regular
      push Not at hlow
      have hreg : ∀ z, H.degree z = k := fun z => le_antisymm (hdeg z) (hlow z)
      have hpos : 0 < Fintype.card V := by omega
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
      obtain ⟨x, hxN, y, hyN, hxy, hxyne⟩ :=
        exists_nonadj_of_cliqueFree H hcf (hreg v)
      have hxv : H.Adj v x := (SimpleGraph.mem_neighborFinset H v x).mp hxN
      have hyv : H.Adj v y := (SimpleGraph.mem_neighborFinset H v y).mp hyN
      -- seed path [x, v, y] and its maximal extension
      have hseednd : ([x, v, y] : List V).Nodup := by
        have h1 : x ≠ v := (H.ne_of_adj hxv).symm
        have h2 : v ≠ y := H.ne_of_adj hyv
        simp [List.nodup_cons, List.mem_cons, h1, hxyne, h2]
      have hseedch : List.IsChain H.Adj [x, v, y] :=
        List.isChain_cons_cons.mpr ⟨hxv.symm, List.isChain_pair.mpr hyv⟩
      obtain ⟨L, hpre, hLne', hLnd, hLch, hLmax⟩ :=
        exists_maximal_path H [x, v, y] (by simp) hseednd hseedch
      obtain ⟨M, hM⟩ := hpre
      by_cases hAll : ∀ u : V, u ∈ L
      · -- Case 1: the path spans V
        -- a third neighbour w₀ of v
        have hw₀ex : (((H.neighborFinset v).erase x).erase y).Nonempty := by
          apply Finset.card_pos.mp
          have h2 : y ∈ (H.neighborFinset v).erase x :=
            Finset.mem_erase.mpr ⟨fun h => hxyne h.symm, hyN⟩
          have h3 := Finset.card_erase_of_mem h2
          have h4 := Finset.card_erase_of_mem hxN
          rw [SimpleGraph.card_neighborFinset_eq_degree, hreg v] at h4
          omega
        obtain ⟨w₀, hw₀mem⟩ := hw₀ex
        obtain ⟨hw₀y, hw₀mem'⟩ := Finset.mem_erase.mp hw₀mem
        obtain ⟨hw₀x, hw₀N⟩ := Finset.mem_erase.mp hw₀mem'
        have hw₀adj : H.Adj v w₀ := (SimpleGraph.mem_neighborFinset H v w₀).mp hw₀N
        -- w₀ sits inside M
        have hw₀L := hAll w₀
        rw [← hM] at hw₀L
        have hw₀M : w₀ ∈ M := by
          simp only [List.cons_append, List.nil_append, List.mem_cons] at hw₀L
          rcases hw₀L with h | h | h | h
          · exact absurd h hw₀x
          · exact absurd h (H.ne_of_adj hw₀adj).symm
          · exact absurd h hw₀y
          · exact h
        obtain ⟨M₁, M₂, hMsplit⟩ := List.append_of_mem hw₀M
        subst hMsplit
        rw [← hM] at hLnd hLch
        have hAll' : ∀ u : V, u ∈ x :: v :: y :: (M₁ ++ w₀ :: M₂) := by
          intro u
          have := hAll u
          rw [← hM] at this
          exact this
        exact colorable_of_spanning_path H hk hdeg hxy hxv hyv hw₀adj hLnd hLch hAll'
      · -- Case 2: a vertex lies off the path; the cycle argument
        push Not at hAll
        obtain ⟨z₀, hz₀⟩ := hAll
        -- e := the last path vertex; all its neighbours are on L
        set e := L.getLast hLne' with he'
        have hLlast : L.getLast? = some e := by
          rw [he']
          exact List.getLast?_eq_some_getLast hLne'
        -- e has a neighbour, and its first one on L opens the cycle
        have hnbre : (H.neighborFinset e).Nonempty := by
          apply Finset.card_pos.mp
          rw [SimpleGraph.card_neighborFinset_eq_degree, hreg e]
          omega
        obtain ⟨w₁, hw₁⟩ := hnbre
        have hw₁adj : H.Adj e w₁ := (SimpleGraph.mem_neighborFinset H e w₁).mp hw₁
        have hexists : ∃ w ∈ L, H.Adj e w := ⟨w₁, hLmax w₁ hw₁adj, hw₁adj⟩
        obtain ⟨T, vj, R, hsplit, hvjadj, hT⟩ := exists_first_split hexists
        -- the cycle D = vj :: R (a suffix of L, closed by the edge e ∼ vj)
        have hDsuf : (vj :: R) <:+ L := ⟨T, hsplit.symm⟩
        have hDnd : (vj :: R).Nodup := hLnd.sublist hDsuf.sublist
        have hDch : List.IsChain H.Adj (vj :: R) := hLch.suffix hDsuf
        have hDlast : (vj :: R).getLast? = some e := by
          have hne'' : (vj :: R) ≠ [] := List.cons_ne_nil _ _
          have h1 : (vj :: R).getLast? = some ((vj :: R).getLast hne'') :=
            List.getLast?_eq_some_getLast hne''
          rw [hsplit, List.getLast?_append, h1, Option.some_or] at hLlast
          rw [h1, hLlast]
        have hememD : e ∈ vj :: R := List.mem_of_getLast? hDlast
        have hDnbrs : ∀ w, H.Adj e w → w ∈ vj :: R := by
          intro w hw
          have hwL : w ∈ L := hLmax w hw
          rw [hsplit] at hwL
          rcases List.mem_append.mp hwL with h | h
          · exact absurd hw (hT w h)
          · exact h
        have hDL : ∀ a ∈ vj :: R, a ∈ L := fun a ha => hDsuf.sublist.subset ha
        have hz₀D : z₀ ∉ (vj :: R).toFinset :=
          fun h => hz₀ (hDL _ (List.mem_toFinset.mp h))
        have heD : e ∈ (vj :: R).toFinset := List.mem_toFinset.mpr hememD
        -- the complement half is smaller (e lives in the cycle)
        have hcardC : Fintype.card ↥(((vj :: R).toFinset)ᶜ) ≤ n := by
          rw [Fintype.card_coe]
          have hsub : ((vj :: R).toFinset)ᶜ ⊆ Finset.univ.erase e := by
            intro a ha
            refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ a⟩
            intro h
            exact (Finset.mem_compl.mp ha) (h ▸ heD)
          have := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem (Finset.mem_univ e), Finset.card_univ] at this
          omega
        by_cases h2a : ∀ w ∈ vj :: R, ∀ z, ¬(z ∈ vj :: R) → ¬H.Adj w z
        · -- Subcase 2a: no edge leaves the cycle; colour both halves by induction
          have hcrossS : ∀ u w, H.Adj u w →
              u ∈ (vj :: R).toFinset → w ∈ (vj :: R).toFinset := by
            intro u w huw huS
            by_contra hwS
            exact h2a u (List.mem_toFinset.mp huS) w
              (fun hw => hwS (List.mem_toFinset.mpr hw)) huw
          have hcardD : Fintype.card ↥((vj :: R).toFinset) ≤ n := by
            rw [Fintype.card_coe]
            have hsub : (vj :: R).toFinset ⊆ Finset.univ.erase z₀ := by
              intro a ha
              exact Finset.mem_erase.mpr ⟨fun h => hz₀D (h ▸ ha), Finset.mem_univ a⟩
            have := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem (Finset.mem_univ z₀), Finset.card_univ] at this
            omega
          exact colorable_of_no_cross H ((vj :: R).toFinset) hcrossS
            (IH (H.comap (Subtype.val : ↥((vj :: R).toFinset) → V)) hcardD
              (fun a => le_trans (degree_comap_le H _ a) (hdeg a.val))
              (Brooks.cliqueFree_comap H _ hcf))
            (IH (H.comap (Subtype.val : ↥(((vj :: R).toFinset)ᶜ) → V)) hcardC
              (fun a => le_trans (degree_comap_le H _ a) (hdeg a.val))
              (Brooks.cliqueFree_comap H _ hcf))
        · -- Subcase 2b: some cycle vertex sees outside; take the LAST such
          push Not at h2a
          have hrev : ∃ w ∈ (vj :: R).reverse, ∃ z, ¬(z ∈ vj :: R) ∧ H.Adj w z := by
            obtain ⟨w, hwD, z, hz1, hz2⟩ := h2a
            exact ⟨w, List.mem_reverse.mpr hwD, z, hz1, hz2⟩
          obtain ⟨T₂, vl, R₂, hsplit₂, hpvl, hT₂⟩ := exists_first_split hrev
          have hD2 : vj :: R = R₂.reverse ++ vl :: T₂.reverse := by
            have h := congrArg List.reverse hsplit₂
            rw [List.reverse_reverse] at h
            rw [h]
            simp [List.reverse_append, List.reverse_cons, List.append_assoc]
          have hD₂no : ∀ w ∈ T₂.reverse, ¬∃ z, ¬(z ∈ vj :: R) ∧ H.Adj w z :=
            fun w hw => hT₂ w (List.mem_reverse.mp hw)
          obtain ⟨u₀, hu₀D, hu₀adj⟩ := hpvl
          -- e is not vl (e's neighbours all lie in the cycle), so T₂.reverse ≠ []
          have hpe : ¬∃ z, ¬(z ∈ vj :: R) ∧ H.Adj e z := by
            rintro ⟨z, hz1, hz2⟩
            exact hz1 (hDnbrs z hz2)
          have hevl : e ≠ vl := by
            intro h
            exact hpe ⟨u₀, hu₀D, h ▸ hu₀adj⟩
          have hD₂ne : T₂.reverse ≠ [] := by
            intro h
            rw [h] at hD2
            rw [hD2, List.getLast?_concat] at hDlast
            exact hevl (Option.some.inj hDlast).symm
          obtain ⟨vl1, D₂', hD₂cons⟩ := List.exists_cons_of_ne_nil hD₂ne
          have hDfull : vj :: R = R₂.reverse ++ vl :: vl1 :: D₂' := by
            rw [hD2, hD₂cons]
          -- vl1's neighbours all lie in the cycle
          have hvl1in : vl1 ∈ T₂.reverse := by
            rw [hD₂cons]
            exact List.mem_cons_self
          have hins : ∀ w, H.Adj vl1 w → w ∈ R₂.reverse ++ vl :: vl1 :: D₂' := by
            intro w hw
            rw [← hDfull]
            by_contra hwD
            exact hD₂no vl1 hvl1in ⟨w, hwD, hw⟩
          -- transport the cycle facts to the decomposition
          rw [hDfull] at hDnd hDch
          have hclose : ∀ e' ∈ (R₂.reverse ++ vl :: vl1 :: D₂').getLast?,
              ∀ hd ∈ (R₂.reverse ++ vl :: vl1 :: D₂').head?, H.Adj e' hd := by
            intro e' he' hd hhd
            rw [← hDfull] at he' hhd
            rw [hDlast, Option.mem_some_iff] at he'
            rw [List.head?_cons, Option.mem_some_iff] at hhd
            rw [← he', ← hhd]
            exact hvjadj
          have hu₀D' : u₀ ∉ R₂.reverse ++ vl :: vl1 :: D₂' := by
            rw [← hDfull]
            exact hu₀D
          -- colour the complement of the cycle by induction
          obtain ⟨f⟩ := IH
            (H.comap (Subtype.val : ↥(((vj :: R).toFinset)ᶜ) → V)) hcardC
            (fun a => le_trans (degree_comap_le H _ a) (hdeg a.val))
            (Brooks.cliqueFree_comap H _ hcf)
          have hsupp : ∀ z, partialOf (((vj :: R).toFinset)ᶜ) (fun a => f a) z = none ↔
              z ∈ R₂.reverse ++ vl :: vl1 :: D₂' := by
            intro z
            rw [partialOf_eq_none_iff, ← hDfull]
            simp only [Finset.mem_compl, not_not, List.mem_toFinset]
          exact colorable_of_cycle_patch H hdeg hDnd hDch hclose hu₀D' hu₀adj hins
            (partialOf (((vj :: R).toFinset)ᶜ) (fun a => f a))
            (partialOf_pproper H _ f) hsupp

/-- **Brooks' theorem, Zając's exception-free disconnected form**
(arXiv:1805.11176): for `k ≥ 3`, `Δ(H) ≤ k` and no `K_{k+1}` imply `H` is
`k`-colourable. -/
theorem brooks_zajac (k : ℕ) (hk : 3 ≤ k) {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ z, H.degree z ≤ k)
    (hcf : H.CliqueFree (k + 1)) : H.Colorable k :=
  brooks_strong k hk (Fintype.card V) H le_rfl hdeg hcf


#print axioms brooks_zajac
end Gebendorfer.Zajac
