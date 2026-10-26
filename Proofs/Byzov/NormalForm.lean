module

public import Proofs.Byzov.Automorphisms

/-! # Exact normal form of every relation automorphism

Every automorphism is uniquely a coordinate translation followed by independent
exchanges of the two members of each intrinsic twin class. No group-order
comparison, bounded enumeration or assumed structural classification is used.
-/

@[expose] public section
namespace ByzovPushkarev.Certificate

def twin {n : ℕ} (t : C n) : Bool → V n
  | false => (3,t)
  | true => (4,t-1)

@[simp] theorem canon_twin {n : ℕ} (t : C n) (b : Bool) : canon (twin t b) = (3,t) := by
  cases b <;> simp [twin,canon]

@[simp] theorem mate_twin {n : ℕ} (t : C n) (b : Bool) : mate (twin t b) = twin t (!b) := by
  cases b <;> simp [twin,mate]

theorem twin_false_ne_true {n : ℕ} (t : C n) : twin t false ≠ twin t true := by
  intro h
  exact (by decide : (3 : Fin 9) ≠ 4) (congrArg Prod.fst h)

theorem exists_twin {n : ℕ} (u : V n) (hu : isTwin u) :
    ∃ t b, u = twin t b := by
  obtain ⟨i,z⟩ := u
  obtain h|h := hu
  · change i = 3 at h
    subst i
    exact ⟨z,false,rfl⟩
  · change i = 4 at h
    subst i
    exact ⟨z+1,true,by simp [twin]⟩

theorem fiber_normal_form {n : ℕ} (g : V n ≃ V n)
    (hg : ∀ u, canon (g u) = canon u) :
    ∃ f : C n → ZMod 2, ∀ u, g u = swap f u := by
  classical
  let f : C n → ZMod 2 := fun t => if g (twin t false) = twin t false then 0 else 1
  have hp : ∀ t b, g (twin t b) = twin t false ∨ g (twin t b) = twin t true := by
    intro t b
    have hk : canon (g (twin t b)) = canon (twin t false) := by rw [hg,canon_twin,canon_twin]
    obtain h|h := canon_fiber (twin t false) (g (twin t b)) hk.symm
    · exact Or.inl h
    · exact Or.inr (by simpa only [mate_twin,Bool.not_false] using h)
  have hb : ∀ t b, g (twin t b) = swap f (twin t b) := by
    intro t b
    have hne : g (twin t false) ≠ g (twin t true) :=
      g.injective.ne (twin_false_ne_true t)
    by_cases h0 : g (twin t false) = twin t false
    · have h1 : g (twin t true) = twin t true := by
        obtain h|h := hp t true
        · exact False.elim (hne (h0.trans h.symm))
        · exact h
      have hft : f t = 0 := if_pos h0
      cases b
      · simpa [swap,hft] using h0
      · simpa [swap,hft] using h1
    · have h0' : g (twin t false) = twin t true := (hp t false).resolve_left h0
      have h1 : g (twin t true) = twin t false := by
        obtain h|h := hp t true
        · exact h
        · exact False.elim (hne (h0'.trans h.symm))
      have hft : f t = 1 := if_neg h0
      cases b
      · simpa [swap,hft] using h0'
      · simpa [swap,hft] using h1
  refine ⟨f,?_⟩
  intro u
  by_cases hu : isTwin u
  · obtain ⟨t,b,rfl⟩ := exists_twin u hu
    exact hb t b
  · have hm : mate u = u := by
      by_contra h
      exact hu ((mate_ne_self u).1 h)
    have hgu : g u = u := by
      obtain h|h := canon_fiber u (g u) (hg u).symm
      · exact h
      · exact h.trans hm
    simp only [swap,hm,ite_self,hgu]

def parameterAut (n : ℕ) (hn : 2 ≤ n) (f : C n → ZMod 2) (a : C n) : Aut n :=
  (translationAut n (-a)).trans (swapAut n hn f)

@[simp] theorem parameterAut_apply (n : ℕ) (hn : 2 ≤ n)
    (f : C n → ZMod 2) (a : C n) (u : V n) :
    parameterAut n hn f a u = swap f (translate (-a) u) := rfl

theorem parameterAut_surjective (n : ℕ) (hn : 2 ≤ n) (e : Aut n) :
    ∃ f a, parameterAut n hn f a = e := by
  let c := sigma n e 0
  let g : V n ≃ V n := (translationAut n (-c)).toEquiv.trans e.toEquiv
  have hg : ∀ u, canon (g u) = canon u := by
    intro u
    change canon (e (translate (-c) u)) = canon u
    have h := aut_canon_translate n hn e (translate (-c) u)
    simpa only [c,translate_translate,add_neg_cancel,translate_zero] using h
  obtain ⟨f,hf⟩ := fiber_normal_form g hg
  refine ⟨f,-c,?_⟩
  apply RelIso.ext
  intro u
  have h := hf (translate c u)
  change e (translate (-c) (translate c u)) = swap f (translate c u) at h
  simpa only [parameterAut_apply,neg_neg,translate_translate,neg_add_cancel,translate_zero] using h.symm

theorem swap_function_injective {n : ℕ} (f g : C n → ZMod 2)
    (h : ∀ u : V n, swap f u = swap g u) : f = g := by
  funext t
  obtain hf|hf := binary_cases (f t)
  · obtain hg|hg := binary_cases (g t)
    · exact hf.trans hg.symm
    · have hh := congrArg Prod.fst (h (3,t))
      simp [swap,canon,mate,hf,hg] at hh
  · obtain hg|hg := binary_cases (g t)
    · have hh := congrArg Prod.fst (h (3,t))
      simp [swap,canon,mate,hf,hg] at hh
    · exact hf.trans hg.symm

theorem parameterAut_injective (n : ℕ) (hn : 2 ≤ n)
    (f g : C n → ZMod 2) (a b : C n)
    (h : parameterAut n hn f a = parameterAut n hn g b) : f = g ∧ a = b := by
  have hc := congrArg (fun e : Aut n => (e ((0,0) : V n)).2) h
  have ha : a = b := by
    simp [parameterAut,translationAut,swapAut,swap,translate,canon,mate] at hc
    exact hc
  subst b
  refine ⟨swap_function_injective f g ?_,rfl⟩
  intro u
  have hu := congrArg (fun e : Aut n => e (translate a u)) h
  simpa only [parameterAut_apply,translate_translate,neg_add_cancel,translate_zero] using hu

end ByzovPushkarev.Certificate
