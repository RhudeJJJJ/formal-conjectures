import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace WOWIIGeometry
lemma increasing_tail (f : ℕ → ℕ) (N a : ℕ)
    (hp : ∀ j, j + 2 ≤ N → f (j+1) + 1 ≤ max (f j) (f (j+2)))
    (ha : a < N) (hs : f a + 1 ≤ f (a+1)) :
    f a + (N-a) ≤ f N := by
  have hstep : ∀ b, a ≤ b → b < N → f b + 1 ≤ f (b+1) := by
    intro b hab
    induction b, hab using Nat.le_induction with
    | base => intro _; exact hs
    | succ b hab ih =>
      intro hb
      have hprev := ih (by omega)
      have h := hp b (by omega)
      omega
  have hbound : ∀ k, k ≤ N-a → f a + k ≤ f (a+k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have hv := ih (by omega)
      have hs' := hstep (a+k) (by omega) (by omega)
      omega
  have h := hbound (N-a) (by omega)
  have he : a+(N-a)=N := by omega
  rwa [he] at h

lemma path_cone (f : ℕ → ℕ) (N : ℕ)
    (hp : ∀ j, j + 2 ≤ N → f (j+1) + 1 ≤ max (f j) (f (j+2)))
    (i : ℕ) (hi : i ≤ N) :
    f i + i ≤ f 0 ∨ f i + (N-i) ≤ f N := by
  by_cases hi0 : i=0
  · subst i; exact Or.inl (by omega)
  by_cases hiN : i=N
  · subst i; exact Or.inr (by omega)
  by_cases hs : f i + 1 ≤ f (i+1)
  · exact Or.inr (increasing_tail f N i hp (by omega) hs)
  have hleft : f i + 1 ≤ f (i-1) := by
    have h := hp (i-1) (by omega)
    have e1 : i-1+1=i := by omega
    have e2 : i-1+2=i+1 := by omega
    rw [e1,e2] at h
    omega
  let g : ℕ → ℕ := fun j => f (N-j)
  have hg : ∀ j, j+2 ≤ N → g (j+1)+1 ≤ max (g j) (g (j+2)) := by
    intro j hj
    have h := hp (N-(j+2)) (by omega)
    have e1 : N-(j+2)+1=N-(j+1) := by omega
    have e2 : N-(j+2)+2=N-j := by omega
    dsimp [g]
    rw [e1,e2,max_comm] at h
    exact h
  have e1 : N-(N-i)=i := by omega
  have e2 : N-(N-i+1)=i-1 := by omega
  have hsg : g (N-i)+1 ≤ g (N-i+1) := by
    simpa only [g,e1,e2] using hleft
  have h := increasing_tail g N (N-i) hg (by omega) hsg
  dsimp [g] at h
  rw [e1, Nat.sub_self, e1] at h
  exact Or.inl h
end WOWIIGeometry
