module

public import Proofs.Byzov.Shape

/-! # Canonical fibers, twin exchange and coordinate translations

The only non-singleton canonical fibers are (3,t) and (4,t-1).
This module is finite-fiber algebra; the actual relation bridge is separate.
-/

@[expose] public section
namespace ByzovPushkarev.Certificate

def isTwin {n : ℕ} (u : V n) : Prop := u.1 = 3 ∨ u.1 = 4
instance {n : ℕ} (u : V n) : Decidable (isTwin u) := inferInstanceAs (Decidable (_ ∨ _))

def mate {n : ℕ} (u : V n) : V n :=
  if u.1 = 3 then (4,u.2-1) else if u.1 = 4 then (3,u.2+1) else u

def translate {n : ℕ} (c : C n) (u : V n) : V n := (u.1,u.2+c)

@[simp] theorem canon_idem {n : ℕ} (u : V n) : canon (canon u) = canon u := by
  by_cases h : u.1 = 4 <;> simp [canon,h]

@[simp] theorem mate_mate {n : ℕ} (u : V n) : mate (mate u) = u := by
  obtain ⟨i,z⟩ := u
  by_cases h3 : i = 3
  · subst i; simp [mate]
  · by_cases h4 : i = 4
    · subst i; simp [mate]
    · simp [mate,h3,h4]

@[simp] theorem canon_mate {n : ℕ} (u : V n) : canon (mate u) = canon u := by
  obtain ⟨i,z⟩ := u
  by_cases h3 : i = 3
  · subst i; simp [mate,canon]
  · by_cases h4 : i = 4
    · subst i; simp [mate,canon]
    · simp [mate,canon,h3,h4]

theorem mate_ne_self {n : ℕ} (u : V n) : mate u ≠ u ↔ isTwin u := by
  obtain ⟨i,z⟩ := u
  by_cases h3 : i = 3
  · subst i; simp [mate,isTwin]
  · by_cases h4 : i = 4
    · subst i; simp [mate,isTwin]
    · simp [mate,isTwin,h3,h4]

theorem canon_fiber {n : ℕ} (u v : V n) (h : canon u = canon v) :
    v = u ∨ v = mate u := by
  obtain ⟨i,z⟩ := u
  obtain ⟨j,w⟩ := v
  by_cases hi : i = 4
  · subst i
    by_cases hj : j = 4
    · subst j
      have hh : z+1 = w+1 := congrArg Prod.snd h
      have he := add_right_cancel hh
      left; simp [he]
    · right
      have hh : ((3 : Fin 9),z+1) = (j,w) := by simpa [canon,hj] using h
      simpa [mate] using hh.symm
  · by_cases hj : j = 4
    · subst j
      have hh : (i,z) = ((3 : Fin 9),w+1) := by simpa [canon,hi] using h
      have hi3 : i = 3 := congrArg Prod.fst hh
      have hz : z = w+1 := congrArg Prod.snd hh
      right
      simp [mate,hi3,hz]
    · left
      simpa [canon,hi,hj] using h.symm

theorem isTwin_of_fiber {n : ℕ} (u v : V n) (h : canon u = canon v) (hne : v ≠ u) :
    isTwin u := by
  obtain hv | hv := canon_fiber u v h
  · exact False.elim (hne hv)
  · exact (mate_ne_self u).1 (by simpa only [← hv] using hne)

theorem canon_fst_of_isTwin {n : ℕ} (u : V n) (h : isTwin u) : (canon u).1 = 3 := by
  obtain h | h := h <;> simp [canon,h]

@[simp] theorem translate_translate {n : ℕ} (a b : C n) (u : V n) :
    translate a (translate b u) = translate (a+b) u := by
  apply Prod.ext
  · rfl
  · change (u.2+b)+a = u.2+(a+b)
    ring

@[simp] theorem translate_zero {n : ℕ} (u : V n) : translate 0 u = u := by
  obtain ⟨i,z⟩ := u; simp [translate]

theorem canon_translate {n : ℕ} (c : C n) (u : V n) :
    canon (translate c u) = translate c (canon u) := by
  obtain ⟨i,z⟩ := u
  by_cases h : i = 4
  · subst i
    change ((3 : Fin 9),(z+c)+1) = ((3 : Fin 9),(z+1)+c)
    congr 1
    ring
  · simp [canon,translate,h]

theorem mate_translate {n : ℕ} (c : C n) (u : V n) :
    mate (translate c u) = translate c (mate u) := by
  obtain ⟨i,z⟩ := u
  by_cases h3 : i = 3
  · subst i
    change ((4 : Fin 9),(z+c)-1) = ((4 : Fin 9),(z-1)+c)
    congr 1
    ring
  · by_cases h4 : i = 4
    · subst i
      change ((3 : Fin 9),(z+c)+1) = ((3 : Fin 9),(z+1)+c)
      congr 1
      ring
    · simp [mate,translate,h3,h4]

theorem binary_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

def swap {n : ℕ} (f : C n → ZMod 2) (u : V n) : V n :=
  if f (canon u).2 = 1 then mate u else u

@[simp] theorem canon_swap {n : ℕ} (f : C n → ZMod 2) (u : V n) :
    canon (swap f u) = canon u := by
  by_cases h : f (canon u).2 = 1 <;> simp [swap,h]

@[simp] theorem swap_swap {n : ℕ} (f : C n → ZMod 2) (u : V n) :
    swap f (swap f u) = u := by
  by_cases h : f (canon u).2 = 1 <;> simp [swap,h]

@[simp] theorem swap_zero {n : ℕ} (u : V n) : swap (fun _ => 0) u = u := by
  simp [swap]

theorem swap_add {n : ℕ} (f g : C n → ZMod 2) (u : V n) :
    swap (fun t => f t+g t) u = swap f (swap g u) := by
  obtain hf | hf := binary_cases (f (canon u).2)
  all_goals obtain hg | hg := binary_cases (g (canon u).2)
  all_goals simp [swap,hf,hg]

theorem translate_swap {n : ℕ} (c : C n) (f : C n → ZMod 2) (u : V n) :
    translate c (swap f u) = swap (fun t => f (t-c)) (translate c u) := by
  have hk : (canon (translate c u)).2-c = (canon u).2 := by
    rw [canon_translate]
    change ((canon u).2+c)-c = (canon u).2
    exact add_sub_cancel_right _ _
  by_cases h : f (canon u).2 = 1
  · have ht : (fun t => f (t-c)) (canon (translate c u)).2 = 1 := by
      change f ((canon (translate c u)).2-c) = 1
      rw [hk]
      exact h
    simp only [swap,if_pos h,if_pos ht]
    exact (mate_translate c u).symm
  · have ht : (fun t => f (t-c)) (canon (translate c u)).2 ≠ 1 := by
      change f ((canon (translate c u)).2-c) ≠ 1
      rw [hk]
      exact h
    simp only [swap,if_neg h,if_neg ht]

end ByzovPushkarev.Certificate
