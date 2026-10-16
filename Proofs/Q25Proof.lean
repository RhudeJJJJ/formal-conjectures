import FormalConjectures.Paper.DasGhoshPrabhuSenHomomorphicPolynomial

/-! A direct bijection on the actual homomorphic pairs, for every color count.
The finite coloring discrepancy is checked separately. No partition-count
formula or polynomial interpolation is assumed. OpenAI Codex assisted. -/
namespace Q25Proof
open DasGhoshPrabhuSen

def setDir {α : Type*} [DecidableEq α] (T : α → α → Bool)
    (a b : α) (k : Bool) (i j : α) : Bool :=
  if i = a ∧ j = b then k else if i = b ∧ j = a then !k else T i j

def pivotH {α : Type*} [DecidableEq α] (T : α → α → Bool) (a c d : α) :=
  setDir (setDir T a c (T a d)) a d true

def pivotG {α : Type*} [DecidableEq α] (T : α → α → Bool) (a c d : α) :=
  setDir (setDir T a d (T a c)) a c true

def replaceLast {α : Type*} (c : Fin 4 → α) (t : α) (v : Fin 4) : α :=
  if v = 3 then t else c v

lemma image_iff {α : Type*} (c : Fin 4 → α) (i : α) :
    (∃ v, c v = i) ↔ c 0 = i ∨ c 1 = i ∨ c 2 = i ∨ c 3 = i := by
  constructor
  · rintro ⟨v, hv⟩
    fin_cases v <;> simp_all
  · rintro (h | h | h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩

lemma tournament_reverse {x : ℕ} {c : Fin 4 → Fin x} {T}
    (ht : IsTournamentOnImage c T) {a b : Fin x}
    (ha : ∃ u, c u = a) (hb : ∃ u, c u = b) (hne : a ≠ b) :
    T b a = !(T a b) := by
  have h := ht.2 a b ha hb hne
  cases h1 : T a b <;> cases h2 : T b a <;> simp_all

lemma tournament_asymm {x : ℕ} {c : Fin 4 → Fin x} {T}
    (ht : IsTournamentOnImage c T) {a b : Fin x} (h : T a b = true) :
    T b a = false := by
  obtain ⟨hne, ha, hb⟩ := ht.1 a b h
  simpa [h] using tournament_reverse ht ha hb hne

lemma setDir_tournament {x : ℕ} {c : Fin 4 → Fin x} {T}
    (ht : IsTournamentOnImage c T) {a b : Fin x}
    (ha : ∃ u, c u = a) (hb : ∃ u, c u = b) (hne : a ≠ b) (k : Bool) :
    IsTournamentOnImage c (setDir T a b k) := by
  constructor
  · intro i j hij
    by_cases hab : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hab
      exact ⟨hne, ha, hb⟩
    by_cases hba : i = b ∧ j = a
    · obtain ⟨rfl, rfl⟩ := hba
      exact ⟨hne.symm, hb, ha⟩
    exact ht.1 i j (by simpa [setDir, hab, hba] using hij)
  · intro i j hi hj hij
    have h := ht.2 i j hi hj hij
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      by_cases hja : j = a <;> by_cases hjb : j = b <;>
      cases k <;> simp_all [setDir]

lemma same_image_tournament {x : ℕ} {c c' : Fin 4 → Fin x} {T}
    (ht : IsTournamentOnImage c T)
    (himage : ∀ i, (∃ v, c v = i) ↔ ∃ v, c' v = i) :
    IsTournamentOnImage c' T := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    obtain ⟨hne, hi, hj⟩ := ht.1 i j hij
    exact ⟨hne, (himage i).mp hi, (himage j).mp hj⟩
  · intro i j hi hj hne
    exact ht.2 i j ((himage i).mpr hi) ((himage j).mpr hj) hne

lemma g_iff {x : ℕ} (c : Fin 4 → Fin x) (T) :
    IsHomomorphicPair witnessG c T ↔ IsTournamentOnImage c T ∧
      T (c 0) (c 1) = true ∧ T (c 0) (c 2) = true ∧ T (c 1) (c 2) = true := by
  constructor
  · intro h
    exact ⟨h.1, h.2 0 1 (by decide), h.2 0 2 (by decide), h.2 1 2 (by decide)⟩
  · rintro ⟨ht, h01, h02, h12⟩
    refine ⟨ht, ?_⟩
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all [witnessG]

lemma h_iff {x : ℕ} (c : Fin 4 → Fin x) (T) :
    IsHomomorphicPair witnessH c T ↔ IsTournamentOnImage c T ∧
      T (c 0) (c 1) = true ∧ T (c 1) (c 2) = true ∧ T (c 0) (c 3) = true := by
  constructor
  · intro h
    exact ⟨h.1, h.2 0 1 (by decide), h.2 1 2 (by decide), h.2 0 3 (by decide)⟩
  · rintro ⟨ht, h01, h12, h03⟩
    refine ⟨ht, ?_⟩
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all [witnessH]

lemma core_distinct {x : ℕ} {c : Fin 4 → Fin x} {T}
    (ht : IsTournamentOnImage c T)
    (h01 : T (c 0) (c 1) = true) (h12 : T (c 1) (c 2) = true) :
    c 0 ≠ c 1 ∧ c 0 ≠ c 2 ∧ c 1 ≠ c 2 := by
  have h10 := tournament_asymm ht h01
  refine ⟨(ht.1 _ _ h01).1, ?_, (ht.1 _ _ h12).1⟩
  intro heq
  rw [← heq, h10] at h12
  contradiction

def toH {x : ℕ} (p : (Fin 4 → Fin x) × (Fin x → Fin x → Bool)) :=
  if p.1 3 = p.1 0 then
    (replaceLast p.1 (p.1 1), setDir p.2 (p.1 0) (p.1 2) false)
  else (p.1, pivotH p.2 (p.1 0) (p.1 2) (p.1 3))

def toG {x : ℕ} (p : (Fin 4 → Fin x) × (Fin x → Fin x → Bool)) :=
  if p.1 3 = p.1 1 ∧ p.2 (p.1 0) (p.1 2) = false then
    (replaceLast p.1 (p.1 0), setDir p.2 (p.1 0) (p.1 2) true)
  else (p.1, pivotG p.2 (p.1 0) (p.1 2) (p.1 3))

lemma toH_valid {x : ℕ} (p : (Fin 4 → Fin x) × (Fin x → Fin x → Bool))
    (hp : IsHomomorphicPair witnessG p.1 p.2) :
    IsHomomorphicPair witnessH (toH p).1 (toH p).2 := by
  obtain ⟨ht, h01, h02, h12⟩ := (g_iff _ _).mp hp
  obtain ⟨hab, hac, hbc⟩ := core_distinct ht h01 h12
  by_cases hd : p.1 3 = p.1 0
  · rw [toH, if_pos hd]
    apply (h_iff _ _).mpr
    have ht' := setDir_tournament ht ⟨0, rfl⟩ ⟨2, rfl⟩ hac false
    have hi : ∀ i, (∃ v, p.1 v = i) ↔ ∃ v, replaceLast p.1 (p.1 1) v = i := by
      intro i
      simp only [image_iff]
      simp [replaceLast, hd, or_comm, or_left_comm]
    refine ⟨same_image_tournament ht' hi, ?_⟩
    simp_all [replaceLast, setDir, eq_comm]
  · rw [toH, if_neg hd]
    apply (h_iff _ _).mpr
    have ht' := setDir_tournament ht ⟨0, rfl⟩ ⟨2, rfl⟩ hac (p.2 (p.1 0) (p.1 3))
    refine ⟨setDir_tournament ht' ⟨0, rfl⟩ ⟨3, rfl⟩ (Ne.symm hd) true, ?_⟩
    simp_all [pivotH, setDir, eq_comm]

lemma toG_valid {x : ℕ} (p : (Fin 4 → Fin x) × (Fin x → Fin x → Bool))
    (hp : IsHomomorphicPair witnessH p.1 p.2) :
    IsHomomorphicPair witnessG (toG p).1 (toG p).2 := by
  obtain ⟨ht, h01, h12, h03⟩ := (h_iff _ _).mp hp
  obtain ⟨hab, hac, hbc⟩ := core_distinct ht h01 h12
  have had := (ht.1 _ _ h03).1
  by_cases hd : p.1 3 = p.1 1 ∧ p.2 (p.1 0) (p.1 2) = false
  · rw [toG, if_pos hd]
    apply (g_iff _ _).mpr
    have ht' := setDir_tournament ht ⟨0, rfl⟩ ⟨2, rfl⟩ hac true
    have hi : ∀ i, (∃ v, p.1 v = i) ↔ ∃ v, replaceLast p.1 (p.1 0) v = i := by
      intro i
      simp only [image_iff]
      simp [replaceLast, hd.1, or_comm, or_left_comm]
    refine ⟨same_image_tournament ht' hi, ?_⟩
    simp_all [replaceLast, setDir, eq_comm]
  · rw [toG, if_neg hd]
    apply (g_iff _ _).mpr
    have ht' := setDir_tournament ht ⟨0, rfl⟩ ⟨3, rfl⟩ had (p.2 (p.1 0) (p.1 2))
    refine ⟨setDir_tournament ht' ⟨0, rfl⟩ ⟨2, rfl⟩ hac true, ?_⟩
    by_cases hdb : p.1 3 = p.1 1
    · have h02 : p.2 (p.1 0) (p.1 2) = true := by
        cases h : p.2 (p.1 0) (p.1 2) <;> simp_all
      simp_all [pivotG, setDir, eq_comm]
    · simp_all [pivotG, setDir, eq_comm]

lemma pivot_roundtrip {x : ℕ} {c : Fin 4 → Fin x} {T}
    (ht : IsTournamentOnImage c T) {a b d : Fin x}
    (ha : ∃ v, c v = a) (_hb : ∃ v, c v = b) (hd : ∃ v, c v = d)
    (hab : a ≠ b) (had : a ≠ d) (h : T a b = true) :
    pivotG (pivotH T a b d) a b d = T := by
  have hba := tournament_asymm ht h
  have hda := tournament_reverse ht ha hd had
  funext i j
  by_cases hbd : b = d
  · subst d
    by_cases hia : i = a <;> by_cases hib : i = b <;>
      by_cases hja : j = a <;> by_cases hjb : j = b <;>
      simp_all [pivotG, pivotH, setDir]
  · by_cases hia : i = a <;> by_cases hib : i = b <;> by_cases hid : i = d <;>
      by_cases hja : j = a <;> by_cases hjb : j = b <;> by_cases hjd : j = d <;>
      simp_all [pivotG, pivotH, setDir]

lemma pivot_roundtrip' {x : ℕ} {c : Fin 4 → Fin x} {T}
    (ht : IsTournamentOnImage c T) {a b d : Fin x}
    (ha : ∃ v, c v = a) (hb : ∃ v, c v = b) (hd : ∃ v, c v = d)
    (hab : a ≠ b) (had : a ≠ d) (h : T a d = true) :
    pivotH (pivotG T a b d) a b d = T := by
  exact pivot_roundtrip ht ha hd hb had hab h

lemma setDir_restore {x : ℕ} {c : Fin 4 → Fin x} {T}
    (ht : IsTournamentOnImage c T) {a b : Fin x} (h : T a b = true) :
    setDir (setDir T a b false) a b true = T := by
  have hab := (ht.1 _ _ h).1
  have hba := tournament_asymm ht h
  funext i j
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    by_cases hja : j = a <;> by_cases hjb : j = b <;>
    simp_all [setDir]

lemma setDir_restore' {x : ℕ} {c : Fin 4 → Fin x} {T}
    (ht : IsTournamentOnImage c T) {a b : Fin x}
    (ha : ∃ v, c v = a) (hb : ∃ v, c v = b) (hab : a ≠ b)
    (h : T a b = false) : setDir (setDir T a b true) a b false = T := by
  have hba := tournament_reverse ht ha hb hab
  funext i j
  by_cases hia : i = a <;> by_cases hib : i = b <;>
    by_cases hja : j = a <;> by_cases hjb : j = b <;>
    simp_all [setDir]

lemma toG_toH {x : ℕ} (p : (Fin 4 → Fin x) × (Fin x → Fin x → Bool))
    (hp : IsHomomorphicPair witnessG p.1 p.2) : toG (toH p) = p := by
  obtain ⟨ht, h01, h02, h12⟩ := (g_iff _ _).mp hp
  obtain ⟨hab, hac, hbc⟩ := core_distinct ht h01 h12
  by_cases hd : p.1 3 = p.1 0
  · have hr := setDir_restore ht h02
    apply Prod.ext
    · funext v
      fin_cases v <;> simp_all [toG, toH, replaceLast, setDir]
    · simpa [toG, toH, hd, replaceLast, setDir, hac, hac.symm] using hr
  · have hc : ¬(p.1 3 = p.1 1 ∧
        pivotH p.2 (p.1 0) (p.1 2) (p.1 3) (p.1 0) (p.1 2) = false) := by
      rintro ⟨he, ht'⟩
      simp_all [pivotH, setDir, eq_comm]
    rw [toH, if_neg hd]
    dsimp only [toG]
    rw [if_neg hc]
    apply Prod.ext
    · rfl
    · exact pivot_roundtrip ht ⟨0, rfl⟩ ⟨2, rfl⟩ ⟨3, rfl⟩ hac (Ne.symm hd) h02

lemma toH_toG {x : ℕ} (p : (Fin 4 → Fin x) × (Fin x → Fin x → Bool))
    (hp : IsHomomorphicPair witnessH p.1 p.2) : toH (toG p) = p := by
  obtain ⟨ht, h01, h12, h03⟩ := (h_iff _ _).mp hp
  obtain ⟨hab, hac, hbc⟩ := core_distinct ht h01 h12
  have had := (ht.1 _ _ h03).1
  by_cases hd : p.1 3 = p.1 1 ∧ p.2 (p.1 0) (p.1 2) = false
  · have hr := setDir_restore' ht ⟨0, rfl⟩ ⟨2, rfl⟩ hac hd.2
    apply Prod.ext
    · funext v
      fin_cases v <;> simp_all [toG, toH, replaceLast]
    · simpa [toG, toH, hd, replaceLast, setDir, hac, hac.symm] using hr
  · rw [toG, if_neg hd]
    dsimp only [toH]
    rw [if_neg (Ne.symm had)]
    apply Prod.ext
    · rfl
    · exact pivot_roundtrip' ht ⟨0, rfl⟩ ⟨2, rfl⟩ ⟨3, rfl⟩ hac had h03

def homEquiv (x : ℕ) :
    {p : (Fin 4 → Fin x) × (Fin x → Fin x → Bool) // IsHomomorphicPair witnessG p.1 p.2} ≃
    {p : (Fin 4 → Fin x) × (Fin x → Fin x → Bool) // IsHomomorphicPair witnessH p.1 p.2} where
  toFun p := ⟨toH p.val, toH_valid p.val p.property⟩
  invFun p := ⟨toG p.val, toG_valid p.val p.property⟩
  left_inv p := Subtype.ext (toG_toH p.val p.property)
  right_inv p := Subtype.ext (toH_toG p.val p.property)

theorem homomorphic_equal (x : ℕ) : homomorphicCount witnessG x = homomorphicCount witnessH x :=
  Nat.card_congr (homEquiv x)


instance (A : Fin 4 → Fin 4 → Bool) (x : ℕ) :
    DecidablePred (IsOrientedColoring A (x := x)) := fun c => by
  unfold IsOrientedColoring
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma counts_three : orientedColoringCount witnessG 3 = 18 ∧
    orientedColoringCount witnessH 3 = 12 := by
  constructor
  · rw [orientedColoringCount, Nat.card_eq_fintype_card]
    decide
  · rw [orientedColoringCount, Nat.card_eq_fintype_card]
    decide

theorem question25 : ¬ ∀ (V W : Type) [Fintype V] [Fintype W]
    (A : V → V → Bool) (B : W → W → Bool), IsOriented A → IsOriented B →
      (∀ x : ℕ, 0 < x → homomorphicCount A x = homomorphicCount B x) →
        ∀ x : ℕ, 0 < x → orientedColoringCount A x = orientedColoringCount B x := by
  intro h
  have he := h (Fin 4) (Fin 4) witnessG witnessH
    witnessG_isOriented witnessH_isOriented (fun x _ => homomorphic_equal x) 3 (by norm_num)
  obtain ⟨hg, hh⟩ := counts_three
  omega

end Q25Proof

#print axioms Q25Proof.question25
#print axioms Q25Proof.homomorphic_equal
#print axioms Q25Proof.counts_three
