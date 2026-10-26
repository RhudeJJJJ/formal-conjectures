module

public import Proofs.Kazemi.Parity
public import Mathlib.Data.Fintype.Card

/-! # The binary Hamming-syndrome construction

All nonzero n-bit vectors occur once as columns, with two further zero columns.
An explicit kernel-times-syndrome equivalence gives the kernel size without a
rank assumption. Kernel words receive singleton colors; the remaining words
receive their two parity colors. Both residual colors are proved nonempty.
-/

@[expose] public section
namespace Kazemi.Certificate
open Finset

abbrev Syndrome (n : ℕ) := Fin n → ZMod 2
abbrev Column (n : ℕ) := {a : Syndrome n // a ≠ 0}
abbrev Index (n : ℕ) := Option (Option (Column n))

def columns (n : ℕ) : Index n → Syndrome n
  | none => 0
  | some none => 0
  | some (some a) => a.val

def syndrome {n : ℕ} (x : Vertex (Index n)) : Syndrome n := bitSum (columns n) x

theorem syndrome_add_self (n : ℕ) (a : Syndrome n) : a + a = 0 := by
  funext i
  exact zmod_two_add_self (a i)

@[simp] theorem syndrome_zero (n : ℕ) : syndrome (zeroWord : Vertex (Index n)) = 0 :=
  bitSum_zero _

theorem syndrome_xor {n : ℕ} (x y : Vertex (Index n)) :
    syndrome (wordXor x y) = syndrome x + syndrome y :=
  bitSum_xor (syndrome_add_self n) _ x y

theorem syndrome_flip {n : ℕ} (x : Vertex (Index n)) (i : Index n) :
    syndrome (flip x i) = syndrome x + columns n i :=
  bitSum_flip (syndrome_add_self n) _ x i

def syndromeWord {n : ℕ} (a : Syndrome n) : Vertex (Index n) :=
  if h : a = 0 then zeroWord else singleWord (some (some ⟨a, h⟩))

@[simp] theorem syndrome_syndromeWord {n : ℕ} (a : Syndrome n) :
    syndrome (syndromeWord a) = a := by
  by_cases h : a = 0
  · subst a
    simp [syndromeWord]
  · simp [syndromeWord, h, syndrome, columns]

abbrev Kernel (n : ℕ) := {x : Vertex (Index n) // syndrome x = 0}

def kernelEquiv (n : ℕ) : (Kernel n × Syndrome n) ≃ Vertex (Index n) where
  toFun p := wordXor p.1.val (syndromeWord p.2)
  invFun x := (⟨wordXor x (syndromeWord (syndrome x)), by
    rw [syndrome_xor, syndrome_syndromeWord, syndrome_add_self]⟩, syndrome x)
  left_inv p := by
    obtain ⟨⟨x, hx⟩, a⟩ := p
    have ha : syndrome (wordXor x (syndromeWord a)) = a := by
      rw [syndrome_xor, hx, syndrome_syndromeWord, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change wordXor (wordXor x (syndromeWord a))
        (syndromeWord (syndrome (wordXor x (syndromeWord a)))) = x
      rw [ha, wordXor_twice]
    · exact ha
  right_inv x := wordXor_twice x (syndromeWord (syndrome x))

@[simp] theorem card_syndrome (n : ℕ) : Fintype.card (Syndrome n) = 2^n := by
  simp [Syndrome]

@[simp] theorem card_column (n : ℕ) : Fintype.card (Column n) = 2^n - 1 := by
  change Fintype.card {a : Syndrome n // ¬a = 0} = _
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, card_syndrome]

@[simp] theorem card_index (n : ℕ) : Fintype.card (Index n) = 2^n + 1 := by
  simp only [Index, Fintype.card_option, card_column]
  have hp : 0 < (2 : ℕ)^n := pow_pos (by decide) n
  omega

theorem pow_two_ge_self (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hp : 0 < (2 : ℕ)^n := pow_pos (by decide) n
    omega

@[simp] theorem kernel_card (n : ℕ) : Fintype.card (Kernel n) = 2^(2^n-n+1) := by
  have hc := Fintype.card_congr (kernelEquiv n)
  have hprod : Fintype.card (Kernel n) * 2^n = 2^(2^n+1) := by
    rw [Fintype.card_prod, card_syndrome] at hc
    change Fintype.card (Kernel n) * 2^n = Fintype.card (Index n → Bool) at hc
    rw [Fintype.card_fun, Fintype.card_bool, card_index] at hc
    exact hc
  have hn := pow_two_ge_self n
  have he : (2^n - n + 1) + n = 2^n + 1 := by omega
  have hg : 2^(2^n-n+1) * 2^n = (2 : ℕ)^(2^n+1) := by rw [← pow_add, he]
  exact mul_right_cancel₀ (ne_of_gt (pow_pos (by decide : 0 < (2 : ℕ)) n)) (hprod.trans hg.symm)

theorem kernel_neighbor (n : ℕ) (x : Vertex (Index n)) :
    ∃ w : Kernel n, (cube (Index n)).Adj x w.val := by
  by_cases hx : syndrome x = 0
  · refine ⟨⟨flip x none, ?_⟩, adj_flip x none⟩
    rw [syndrome_flip, columns, hx, add_zero]
  · let i : Index n := some (some ⟨syndrome x, hx⟩)
    refine ⟨⟨flip x i, ?_⟩, adj_flip x i⟩
    rw [syndrome_flip]
    change syndrome x + syndrome x = 0
    exact syndrome_add_self n _

theorem outside_kernel_parity (n : ℕ) (hn : 0 < n) (p : ZMod 2) :
    ∃ x : Vertex (Index n), syndrome x ≠ 0 ∧ parity x = p := by
  let a : Syndrome n := fun _ => 1
  have ha : a ≠ 0 := by
    intro h
    have he := congrFun h (⟨0, hn⟩ : Fin n)
    norm_num [a] at he
  let x := syndromeWord a
  have hx : syndrome x ≠ 0 := by simpa [x] using ha
  by_cases hp : parity x = p
  · exact ⟨x, hx, hp⟩
  · refine ⟨flip x none, ?_, ?_⟩
    · simpa only [syndrome_flip, columns, add_zero] using hx
    · rw [parity_flip]
      exact zmod_two_add_one_of_ne hp

def codeColor {n : ℕ} (x : Vertex (Index n)) : Kernel n ⊕ ZMod 2 :=
  if h : syndrome x = 0 then Sum.inl ⟨x, h⟩ else Sum.inr (parity x)

theorem codeColor_eq_inl_iff {n : ℕ} (x : Vertex (Index n)) (w : Kernel n) :
    codeColor x = Sum.inl w ↔ x = w.val := by
  constructor
  · intro h
    by_cases hx : syndrome x = 0
    · simp only [codeColor, dif_pos hx] at h
      exact congrArg Subtype.val (Sum.inl.inj h)
    · simp only [codeColor, dif_neg hx] at h
      cases h
  · intro h
    subst x
    simp [codeColor, w.property]

theorem codeColor_proper {n : ℕ} {x y : Vertex (Index n)}
    (hxy : (cube (Index n)).Adj x y) : codeColor x ≠ codeColor y := by
  intro h
  by_cases hx : syndrome x = 0
  · have hc : codeColor x = Sum.inl (⟨x, hx⟩ : Kernel n) := by simp [codeColor, hx]
    have hyx : y = x := (codeColor_eq_inl_iff y _).1 (h.symm.trans hc)
    exact hxy.ne hyx.symm
  · by_cases hy : syndrome y = 0
    · have hc : codeColor y = Sum.inl (⟨y, hy⟩ : Kernel n) := by simp [codeColor, hy]
      have hxy' : x = y := (codeColor_eq_inl_iff x _).1 (h.trans hc)
      exact hxy.ne hxy'
    · have hc : parity x = parity y := by
        apply Sum.inr.inj
        simpa only [codeColor, dif_neg hx, dif_neg hy] using h
      exact parity_ne_of_adj hxy hc

theorem codeColor_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (codeColor (n := n)) := by
  intro i
  cases i with
  | inl w => exact ⟨w.val, by simp [codeColor, w.property]⟩
  | inr p =>
    obtain ⟨x, hx, hp⟩ := outside_kernel_parity n hn p
    exact ⟨x, by simp [codeColor, hx, hp]⟩

theorem codeColor_domination (n : ℕ) (x : Vertex (Index n)) :
    ∃ i, ∀ w, codeColor w = i → (cube (Index n)).Adj x w := by
  obtain ⟨w, hw⟩ := kernel_neighbor n x
  refine ⟨Sum.inl w, ?_⟩
  intro y hy
  rw [(codeColor_eq_inl_iff y w).1 hy]
  exact hw

theorem code_coloring (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : Vertex (Index n) → Fin (2^(2^n-n+1)+2),
      (∀ x y, (cube (Index n)).Adj x y → c x ≠ c y) ∧ Function.Surjective c ∧
      (∀ x, ∃ i, ∀ w, c w = i → (cube (Index n)).Adj x w) := by
  classical
  let e : (Kernel n ⊕ ZMod 2) ≃ Fin (2^(2^n-n+1)+2) :=
    Fintype.equivOfCardEq (by simp)
  refine ⟨fun x => e (codeColor x), ?_, ?_, ?_⟩
  · intro x y hxy h
    exact codeColor_proper hxy (e.injective h)
  · exact e.surjective.comp (codeColor_surjective n (by omega))
  · intro x
    obtain ⟨i, hi⟩ := codeColor_domination n x
    exact ⟨e i, fun w hw => hi w (e.injective hw)⟩

end Kazemi.Certificate
