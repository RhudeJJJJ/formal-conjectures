/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanQuadraticDisk
import Proofs.RadenkovicGutmanHighDegreeTail
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Analytic bridge for the original correlated degree-46 escape certificate.
Source: uniform_degree_certificates.py, direct_escape.build_polynomials(42/25,3).
The directed and reserve polynomial signs remain explicit obligations. -/
namespace Gebendorfer.RadenkovicGutman.CorrelatedEscape
open Focus Set
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def quadratic (t : ℝ) : ℝ := 1-t+t^2/2
def cubic (t : ℝ) : ℝ := quadratic t-t^3/6

theorem exp_quadratic_upper (t : ℝ) (ht : 0 ≤ t) : Real.exp (-t) ≤ quadratic t := by
  have hd (x : ℝ) : HasDerivAt (fun s => quadratic s-Real.exp (-s))
      (Real.exp (-x)-1+x) x := by
    have h := (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 2).div_const 2)).sub ((hasDerivAt_id x).neg.exp)
    convert h using 1 <;> simp only [id_eq,quadratic] <;> ring
  have hm := monotone_of_hasDerivAt_nonneg hd (by
    intro x
    linarith only [Real.add_one_le_exp (-x)])
  have h := hm ht
  norm_num [quadratic] at h
  linarith only [h]

theorem cubic_le_exp (t : ℝ) (ht : 0 ≤ t) : cubic t ≤ Real.exp (-t) := by
  have hd (x : ℝ) : HasDerivAt (fun s => Real.exp (-s)-cubic s)
      (quadratic x-Real.exp (-x)) x := by
    have h := ((hasDerivAt_id x).neg.exp).sub
      ((((hasDerivAt_const x 1).sub (hasDerivAt_id x)).add
        (((hasDerivAt_id x).pow 2).div_const 2)).sub
        (((hasDerivAt_id x).pow 3).div_const 6))
    convert h using 1 <;> simp only [id_eq,cubic,quadratic] <;> ring
  have hc : Continuous (fun s : ℝ => Real.exp (-s)-cubic s) :=
    continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
    hc.continuousOn (fun x _ => (hd x).hasDerivWithinAt)
    (fun x hx => sub_nonneg.mpr (exp_quadratic_upper x (interior_subset hx)))
  have h := hm (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
  norm_num [cubic,quadratic] at h
  linarith only [h]

theorem cubic_bounds (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : 0 < cubic t ∧ cubic t ≤ 1 := by
  have h2 : 0 ≤ t^2*(3-t) := mul_nonneg (sq_nonneg t) (by linarith only [ht.2])
  have h3 : 0 ≤ t*(1-t/2+t^2/6) :=
    mul_nonneg ht.1 (by nlinarith only [ht.2,sq_nonneg t])
  dsimp [cubic,quadratic]
  constructor <;> nlinarith only [h2,h3,ht.2]

def lead (y P Q t : ℝ) : ℝ := cubic t*Complex.normSq (A P Q)-Complex.normSq (B y P Q)
def bx (y P Q t : ℝ) : ℝ :=
  2*(cubic t*(A P Q*star (N₀ y P Q)).re-(B y P Q*star (D₀ y P Q)).re)
def bt (y P Q t : ℝ) : ℝ :=
  -2*(cubic t*(A P Q*star (N₀ y P Q)).im-(B y P Q*star (D₀ y P Q)).im)
def constant (y P Q t : ℝ) : ℝ :=
  cubic t*Complex.normSq (N₀ y P Q)-Complex.normSq (D₀ y P Q)
def directed (d y P Q t : ℝ) : ℝ :=
  QuadraticDisk.directed (lead y P Q t) (bx y P Q t) (bt y P Q t)
    (constant y P Q t) (r d y) (g d y)
def reserve (d y P Q t : ℝ) : ℝ :=
  QuadraticDisk.reserve (lead y P Q t) (bx y P Q t) (bt y P Q t)
    (constant y P Q t) (r d y) (g d y)

theorem lead_neg (y P Q t : ℝ) (hy : 0 < y) (hP : y ≤ P) (hQ : y ≤ Q)
    (ht : t ∈ Ico (0 : ℝ) 1) : lead y P Q t < 0 := by
  have he : Complex.normSq (B y P Q)-Complex.normSq (A P Q) = (2*P-y)*(2*Q-y) := by
    simp only [A,B,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im]
    ring
  have hp : 0 < (2*P-y)*(2*Q-y) := mul_pos (by linarith) (by linarith)
  have hm := mul_le_mul_of_nonneg_right (cubic_bounds t ht).2 (Complex.normSq_nonneg (A P Q))
  unfold lead
  nlinarith only [he,hp,hm]

theorem quadratic_identity (y P Q t : ℝ) (ζ : ℂ) :
    cubic t*Complex.normSq (A P Q*ζ+N₀ y P Q)-Complex.normSq (B y P Q*ζ+D₀ y P Q) =
      QuadraticDisk.value (lead y P Q t) (bx y P Q t) (bt y P Q t) (constant y P Q t) ζ := by
  simp only [QuadraticDisk.value,lead,bx,bt,constant,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im]
  ring

theorem log_lower_of_signs (d y P Q t : ℝ) (hd : 0 ≤ d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q) (ht : t ∈ Ico (0 : ℝ) 1)
    (hD : directed d y P Q t ≤ 0) (hR : 0 ≤ reserve d y P Q t)
    (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) : t/2 ≤ Real.log ‖quotient y P Q ζ‖ := by
  have hr : 0 ≤ r d y := by unfold r; positivity
  have hH := QuadraticDisk.concave_nonneg _ _ _ _ _ _ (lead_neg y P Q t hy hP hQ ht)
    hr hD hR ζ hζ
  rw [← quadratic_identity] at hH
  have hm := mul_le_mul_of_nonneg_right (cubic_le_exp t ht.1)
    (Complex.normSq_nonneg (A P Q*ζ+N₀ y P Q))
  have hn : Complex.normSq (B y P Q*ζ+D₀ y P Q) ≤
      Real.exp (-t)*Complex.normSq (A P Q*ζ+N₀ y P Q) := by linarith only [hH,hm]
  have he : Real.exp t*Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have hmul := mul_le_mul_of_nonneg_left hn (Real.exp_pos t).le
  rw [← mul_assoc,he,one_mul] at hmul
  have hb := Complex.normSq_pos.mpr (TailHalfGeometry.denominator_ne_zero d y P Q hy hP hQ ζ hζ)
  have hs : Real.exp t ≤ ‖quotient y P Q ζ‖^2 := by
    rw [quotient,norm_div,div_pow,← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    exact (le_div_iff₀ hb).mpr hmul
  have hl := Real.log_le_log (Real.exp_pos t) hs
  rw [Real.log_exp,Real.log_pow] at hl
  norm_num at hl
  linarith only [hl]

def payment (d x : ℝ) : ℝ := (42/25 : ℝ)/(d*(1+x^2))

theorem payment_range (d x : ℝ) (hd : 46 ≤ d) : payment d x ∈ Ico (0 : ℝ) 1 := by
  have hd0 : 0 < d := by linarith only [hd]
  have hp : 1 ≤ 1+x^2 := by nlinarith only [sq_nonneg x]
  have hm := mul_le_mul_of_nonneg_left hp hd0.le
  constructor
  · unfold payment; positivity
  · unfold payment
    apply (div_lt_one (by positivity : 0 < d*(1+x^2))).mpr
    nlinarith only [hm,hd]

theorem payment_density (d x : ℝ) (hd : 0 < d) :
    payment d x/2 = TailIntegral.escapeDensity d (d*x) := by
  unfold payment TailIntegral.escapeDensity
  field_simp [hd.ne']
  ring

attribute [-instance] SimpleGraph.fintypeEdgeSetSup
open CoreQuotient
open scoped Classical

/-- These are precisely the remaining normalized directed and full-reserve
signs on the original degree-46 parameter box. No signs are asserted here. -/
def Signs (d : ℝ) : Prop :=
  ∀ x ∈ Icc (653/2000 : ℝ) 10, ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
    directed d (d*x) (d*x+a/(d*x)) (d*x+b/(d*x)) (payment d x) ≤ 0 ∧
      0 ≤ reserve d (d*x) (d*x+a/(d*x)) (d*x+b/(d*x)) (payment d x)

theorem graph_lower_of_signs {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 46 ≤ C.degree u)
    (hS : Signs (C.degree u)) (y : ℝ)
    (hy : y ∈ Icc ((653/2000 : ℝ)*(C.degree u : ℝ)) (10*(C.degree u : ℝ))) :
    TailIntegral.escapeDensity (C.degree u) y ≤
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  let d : ℝ := C.degree u
  have hd' : 46 ≤ d := by exact_mod_cast hd
  have hd0 : 0 < d := by linarith only [hd']
  have hy0 : 0 < y := by change _ ≤ y ∧ y ≤ _ at hy; nlinarith only [hy.1,hd']
  have hx : y/d ∈ Icc (653/2000 : ℝ) 10 := by
    constructor
    · exact (le_div_iff₀ hd0).mpr hy.1
    · exact (div_le_iff₀ hd0).mpr (by nlinarith only [hy.2])
  have he : d*(y/d)=y := by field_simp [hd0.ne']
  have ha : PathEnclosure.arm y p ∈ Icc (0 : ℝ) 1 :=
    ⟨PathEnclosure.arm_nonneg y p,PathEnclosure.arm_le_one y hy0 p⟩
  have hb : PathEnclosure.arm y q ∈ Icc (0 : ℝ) 1 :=
    ⟨PathEnclosure.arm_nonneg y q,PathEnclosure.arm_le_one y hy0 q⟩
  obtain ⟨hD,hR⟩ := hS (y/d) hx (PathEnclosure.arm y p) ha (PathEnclosure.arm y q) hb
  rw [he] at hD hR
  have h := log_lower_of_signs d y _ _ _ hd0.le hy0
    (by have h := div_nonneg ha.1 hy0.le; linarith only [h])
    (by have h := div_nonneg hb.1 hy0.le; linarith only [h])
    (payment_range d (y/d) hd') hD hR _ (schur_in_disk C u y hy0).1
  rw [payment_density d (y/d) hd0,he] at h
  change TailIntegral.escapeDensity d y ≤ Real.log ‖(shifted (z y) (source C u p q)).det /
    (shifted (z y) (fused C u p q)).det‖
  rw [concrete_graph_quotient C u y hy0 p q]
  exact h

theorem strict_fusion_of_lowstrip_and_signs {m : ℕ} (C : SimpleGraph (Fin m))
    (u : Fin m) (p q : ℕ) (hT : (source C u p q).IsTree) (hd : 46 ≤ C.degree u)
    (hS : Signs (C.degree u))
    (hlow : (-(8/3 : ℝ)*Real.log 2-2*Real.log 3)/(C.degree u : ℝ)-Real.log 2/2 ≤
      ∫ y : ℝ in (0 : ℝ)..(1/2), MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y) :
    laplacianEnergy (fused C u p q) < laplacianEnergy (source C u p q) := by
  exact HighDegreeTail.strict_fusion_of_lowstrip_escape C u p q hT hd hlow
    (graph_lower_of_signs C u p q hd hS)

#print axioms exp_quadratic_upper
#print axioms cubic_le_exp
#print axioms cubic_bounds
#print axioms lead_neg
#print axioms quadratic_identity
#print axioms log_lower_of_signs
#print axioms payment_range
#print axioms payment_density
#print axioms graph_lower_of_signs
#print axioms strict_fusion_of_lowstrip_and_signs
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.CorrelatedEscape
