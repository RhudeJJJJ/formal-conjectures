module

public import Proofs.Byzov.Source

/-! # The intrinsic twin quotient and its rotation action

Relation automorphisms preserve the exact canonical fibers. Their induced
permutation on the twin classes preserves the tournament and is a rotation.
The two-sided source profiles then determine every remaining vertex.
-/

@[expose] public section
namespace ByzovPushkarev.Certificate

abbrev Aut (n : ℕ) := RelIso (adjacent n) (adjacent n)

def translationAut (n : ℕ) (c : C n) : Aut n where
  toEquiv :=
    { toFun := translate c
      invFun := translate (-c)
      left_inv u := by rw [translate_translate,neg_add_cancel,translate_zero]
      right_inv u := by rw [translate_translate,add_neg_cancel,translate_zero] }
  map_rel_iff' := adjacent_translate n c _ _

def swapAut (n : ℕ) (hn : 2 ≤ n) (f : C n → ZMod 2) : Aut n where
  toEquiv :=
    { toFun := swap f
      invFun := swap f
      left_inv := swap_swap f
      right_inv := swap_swap f }
  map_rel_iff' := by
    intro u v
    have h := adjacent_canon n hn (swap f u) (swap f v)
    rw [canon_swap,canon_swap] at h
    exact h.trans (adjacent_canon n hn u v).symm

theorem map_canon (n : ℕ) (hn : 2 ≤ n) (e : Aut n) (u v : V n)
    (h : canon u = canon v) : canon (e u) = canon (e v) := by
  apply (twins_iff_canon n hn _ _).1
  have ht := (twins_iff_canon n hn u v).2 h
  constructor
  · intro w
    obtain ⟨x,rfl⟩ := e.surjective w
    exact e.map_rel_iff.trans ((ht.1 x).trans e.map_rel_iff.symm)
  · intro w
    obtain ⟨x,rfl⟩ := e.surjective w
    exact e.map_rel_iff.trans ((ht.2 x).trans e.map_rel_iff.symm)

theorem map_isTwin (n : ℕ) (hn : 2 ≤ n) (e : Aut n) (u : V n)
    (hu : isTwin u) : isTwin (e u) := by
  have hk := map_canon n hn e u (mate u) (canon_mate u).symm
  apply isTwin_of_fiber (e u) (e (mate u)) hk
  intro h
  exact (mate_ne_self u).2 hu (e.injective h)

def sigma (n : ℕ) (e : Aut n) (t : C n) : C n := (canon (e (3,t))).2

theorem canon_image_twin (n : ℕ) (hn : 2 ≤ n) (e : Aut n) (t : C n) :
    canon (e (3,t)) = (3,sigma n e t) := by
  apply Prod.ext
  · exact canon_fst_of_isTwin _ (map_isTwin n hn e (3,t) (Or.inl rfl))
  · rfl

def inducedEquiv (n : ℕ) (hn : 2 ≤ n) (e : Aut n) : C n ≃ C n where
  toFun := sigma n e
  invFun := sigma n e.symm
  left_inv t := by
    have h := map_canon n hn e.symm (e (3,t)) (3,sigma n e t) (by
      simpa [canon] using canon_image_twin n hn e t)
    have hh := congrArg Prod.snd h
    simpa [sigma,canon] using hh.symm
  right_inv t := by
    have h := map_canon n hn e (e.symm (3,t)) (3,sigma n e.symm t) (by
      simpa [canon] using canon_image_twin n hn e.symm t)
    have hh := congrArg Prod.snd h
    simpa [sigma,canon] using hh.symm

theorem induced_tournament (n : ℕ) (hn : 2 ≤ n) (e : Aut n) (t s : C n) :
    tournament (n+1) (sigma n e t) (sigma n e s) ↔ tournament (n+1) t s := by
  have h : adjacent n (e (3,t)) (e (3,s)) ↔ adjacent n (3,t) (3,s) := e.map_rel_iff
  rw [adjacent_canon n hn (e (3,t)) (e (3,s)),
    canon_image_twin n hn e t,canon_image_twin n hn e s] at h
  rwa [twin_tournament n hn,twin_tournament n hn] at h

theorem sigma_rotation (n : ℕ) (hn : 2 ≤ n) (e : Aut n) (t : C n) :
    sigma n e t = sigma n e 0+t :=
  tournament_rotation (by omega) (by dsimp [M]; omega)
    (inducedEquiv n hn e) (induced_tournament n hn e) t

theorem adjacent_key_right (n : ℕ) (hn : 2 ≤ n) (u v w : V n)
    (h : canon v = canon w) : adjacent n u v ↔ adjacent n u w := by
  rw [adjacent_canon_right n hn u v,adjacent_canon_right n hn u w,h]

theorem adjacent_key_left (n : ℕ) (u v w : V n)
    (h : canon u = canon v) : adjacent n u w ↔ adjacent n v w := by
  rw [adjacent_canon_left n u w,adjacent_canon_left n v w,h]

theorem aut_canon_translate (n : ℕ) (hn : 2 ≤ n) (e : Aut n) (u : V n) :
    canon (e u) = canon (translate (sigma n e 0) u) := by
  let c := sigma n e 0
  have hpre : ∀ t : C n, canon (e (3,t-c)) = canon ((3,t) : V n) := by
    intro t
    rw [canon_image_twin n hn,sigma_rotation n hn]
    change ((3 : Fin 9),c+(t-c)) = ((3 : Fin 9),t)
    congr 1
    ring
  have ht : ∀ t : C n, translate c ((3,t-c) : V n) = (3,t) := by
    intro t
    apply Prod.ext
    · rfl
    · exact sub_add_cancel t c
  apply profiles_determine_canon n hn
  · rw [← outProfile_eq n (e u),← outProfile_eq n (translate c u)]
    ext t
    simp only [mem_outProfile]
    calc
      adjacent n (e u) (3,t) ↔ adjacent n (e u) (e (3,t-c)) :=
        adjacent_key_right n hn _ _ _ (hpre t).symm
      _ ↔ adjacent n u (3,t-c) := e.map_rel_iff
      _ ↔ adjacent n (translate c u) (3,t) := by
        have h := adjacent_translate n c u (3,t-c)
        rw [ht] at h
        exact h.symm
  · rw [← inProfile_eq n hn (e u),← inProfile_eq n hn (translate c u)]
    ext t
    simp only [mem_inProfile]
    calc
      adjacent n (3,t) (e u) ↔ adjacent n (e (3,t-c)) (e u) :=
        adjacent_key_left n _ _ _ (hpre t).symm
      _ ↔ adjacent n (3,t-c) u := e.map_rel_iff
      _ ↔ adjacent n (3,t) (translate c u) := by
        have h := adjacent_translate n c (3,t-c) u
        rw [ht] at h
        exact h.symm

end ByzovPushkarev.Certificate
