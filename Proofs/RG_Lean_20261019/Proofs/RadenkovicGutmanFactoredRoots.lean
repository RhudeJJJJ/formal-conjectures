/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanCheckedRoots
import Proofs.RadenkovicGutmanIsoEnergy

/-! Complete root boxes with multiplicities, attached to actual graph energies.
The finite witnesses use the squarefree factorization of each Laplacian
characteristic polynomial. Factor identities and graph coverage are separate
obligations; neither is inferred from a list of spectral bounds. -/
namespace Gebendorfer.RadenkovicGutman.FactoredRoots
open Polynomial Finset
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
attribute [-instance] SimpleGraph.fintypeEdgeSetSup

structure Box where
  coefficients : List ℚ
  count : ℕ
  lower : Fin count → ℚ
  upper : Fin count → ℚ
  copies : ℕ

def accepted (b : Box) : Bool :=
  CheckedRoots.accepts b.coefficients b.count b.lower b.upper

def allAccepted (bs : List Box) : Bool := bs.all accepted

def factor (b : Box) : ℝ[X] := CheckedRoots.polynomial b.coefficients ^ b.copies

def product : List Box → ℝ[X]
  | [] => 1
  | b :: bs => factor b * product bs

def mass (p : ℝ[X]) (t : ℝ) : ℝ :=
  (p.roots.map (fun x => max (x-t) 0)).sum

def lower (b : Box) (t : ℝ) : ℝ :=
  b.copies * ∑ i, max ((b.lower i : ℝ)-t) 0
def upper (b : Box) (t : ℝ) : ℝ :=
  b.copies * ∑ i, max ((b.upper i : ℝ)-t) 0
def lowerTotal : List Box → ℝ → ℝ
  | [], _ => 0
  | b :: bs, t => lower b t + lowerTotal bs t
def upperTotal : List Box → ℝ → ℝ
  | [], _ => 0
  | b :: bs, t => upper b t + upperTotal bs t

theorem coefficient_polynomial_ne_zero (b : Box) (hb : accepted b = true) :
    CheckedRoots.polynomial b.coefficients ≠ 0 := by
  have h : 0 < b.count ∧ b.coefficients.length ≤ b.count+1 ∧
      ∀ i, b.lower i < b.upper i ∧
        CheckedRoots.eval b.coefficients (b.lower i)*CheckedRoots.eval b.coefficients (b.upper i)<0 ∧
        ∀ j, i<j → b.upper i≤b.lower j := of_decide_eq_true hb
  have hs := (h.2.2 ⟨0,h.1⟩).2.1
  have hsR : (CheckedRoots.polynomial b.coefficients).eval (b.lower ⟨0,h.1⟩ : ℝ)*
      (CheckedRoots.polynomial b.coefficients).eval (b.upper ⟨0,h.1⟩ : ℝ)<0 := by
    rw [← CheckedRoots.eval_cast,← CheckedRoots.eval_cast]
    exact_mod_cast hs
  intro hz
  simp [hz] at hsR

theorem factor_ne_zero (b : Box) (hb : accepted b=true) : factor b ≠ 0 :=
  pow_ne_zero _ (coefficient_polynomial_ne_zero b hb)

theorem product_ne_zero (bs : List Box) (hb : allAccepted bs=true) : product bs ≠ 0 := by
  induction bs with
  | nil => exact one_ne_zero
  | cons b bs ih =>
    have h : accepted b=true ∧ allAccepted bs=true := by
      simpa only [allAccepted,List.all_cons,Bool.and_eq_true] using hb
    exact mul_ne_zero (factor_ne_zero b h.1) (ih h.2)

theorem mass_mul (p q : ℝ[X]) (hp : p≠0) (hq : q≠0) (t : ℝ) :
    mass (p*q) t=mass p t+mass q t := by
  rw [mass,Polynomial.roots_mul (mul_ne_zero hp hq),Multiset.map_add,Multiset.sum_add]
  rfl

theorem mass_pow (p : ℝ[X]) (k : ℕ) (t : ℝ) : mass (p^k) t=k*mass p t := by
  simp [mass,Polynomial.roots_pow,Multiset.map_nsmul,Multiset.sum_nsmul,nsmul_eq_mul]

theorem box_bounds (b : Box) (hb : accepted b=true) (t : ℝ) :
    lower b t≤mass (factor b) t ∧ mass (factor b) t≤upper b t := by
  have h := CheckedRoots.stop_loss_bounds b.coefficients b.count b.lower b.upper hb t
  rw [factor,mass_pow]
  exact ⟨mul_le_mul_of_nonneg_left h.1 (Nat.cast_nonneg _),
    mul_le_mul_of_nonneg_left h.2 (Nat.cast_nonneg _)⟩

theorem bounds (bs : List Box) (hb : allAccepted bs=true) (t : ℝ) :
    lowerTotal bs t≤mass (product bs) t ∧ mass (product bs) t≤upperTotal bs t := by
  induction bs with
  | nil => simp [lowerTotal,upperTotal,product,mass]
  | cons b bs ih =>
    have h : accepted b=true ∧ allAccepted bs=true := by
      simpa only [allAccepted,List.all_cons,Bool.and_eq_true] using hb
    have hc := box_bounds b h.1 t
    have ht := ih h.2
    rw [product,mass_mul _ _ (factor_ne_zero b h.1) (product_ne_zero bs h.2)]
    exact ⟨add_le_add hc.1 ht.1,add_le_add hc.2 ht.2⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem graph_stopLoss_bounds (G : SimpleGraph V) (bs : List Box)
    (hb : allAccepted bs=true) (hp : (G.lapMatrix ℝ).charpoly=product bs) (t : ℝ) :
    lowerTotal bs t≤stopLoss (laplacianSpectrum G) t ∧
      stopLoss (laplacianSpectrum G) t≤upperTotal bs t := by
  have he : stopLoss (laplacianSpectrum G) t=mass (G.lapMatrix ℝ).charpoly t :=
    IsoEnergy.spectral_sum_roots G (fun x => max (x-t) 0)
  rw [he,hp]
  exact bounds bs hb t

theorem strict_energy (G H : SimpleGraph V) (hG : G.IsTree) (hH : H.IsTree)
    (gs hs : List Box) (hg : allAccepted gs=true) (hh : allAccepted hs=true)
    (hpg : (G.lapMatrix ℝ).charpoly=product gs)
    (hph : (H.lapMatrix ℝ).charpoly=product hs)
    (hgap : upperTotal hs (2-2/(Fintype.card V : ℝ))<
      lowerTotal gs (2-2/(Fintype.card V : ℝ))) :
    laplacianEnergy H<laplacianEnergy G := by
  have hg' := (graph_stopLoss_bounds G gs hg hpg (2-2/(Fintype.card V : ℝ))).1
  have hh' := (graph_stopLoss_bounds H hs hh hph (2-2/(Fintype.card V : ℝ))).2
  rw [tree_energy_identity G hG,tree_energy_identity H hH]
  linarith

def repeatedControl : List Box :=
  [{coefficients := [0,1],count := 1,lower := ![-1/100],upper := ![1/100],copies := 1},
   {coefficients := [-1,1],count := 1,lower := ![99/100],upper := ![101/100],copies := 3}]
theorem repeatedControl_accepted : allAccepted repeatedControl=true := by decide +kernel
theorem repeatedControl_bounds :
    147/100≤mass (product repeatedControl) (1/2) ∧
      mass (product repeatedControl) (1/2)≤153/100 := by
  have h := bounds repeatedControl repeatedControl_accepted (1/2)
  norm_num [repeatedControl,lowerTotal,upperTotal,lower,upper,Fin.sum_univ_succ] at h
  exact h
theorem bad_interval_rejected : accepted
    {coefficients := [-1,1],count := 1,lower := ![2],upper := ![3],copies := 3}=false := by
  decide +kernel

#print axioms coefficient_polynomial_ne_zero
#print axioms product_ne_zero
#print axioms mass_pow
#print axioms bounds
#print axioms graph_stopLoss_bounds
#print axioms strict_energy
#print axioms repeatedControl_accepted
#print axioms repeatedControl_bounds
#print axioms bad_interval_rejected
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.FactoredRoots
