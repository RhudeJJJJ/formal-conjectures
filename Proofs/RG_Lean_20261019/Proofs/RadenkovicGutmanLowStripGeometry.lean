/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanQuadraticDiskConvex
import Proofs.RadenkovicGutmanHighDegreeTail

/-! Original tangent-strip modulus comparison on the same Schur disk.
The outside/directed/full-reserve signs remain explicit hypotheses.
Source: rg_multiarm_small_ordinate_lowstrip.py, build_general_conditions. -/
namespace Gebendorfer.RadenkovicGutman.LowStripGeometry
open Focus Set CoreQuotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

def lead (y P Q c : ℝ) : ℝ :=
  Complex.normSq (A P Q)-(c^2/4)*Complex.normSq (B y P Q)
def bx (y P Q c : ℝ) : ℝ :=
  2*((A P Q*star (N₀ y P Q)).re-(c^2/4)*(B y P Q*star (D₀ y P Q)).re)
def bt (y P Q c : ℝ) : ℝ :=
  -2*((A P Q*star (N₀ y P Q)).im-(c^2/4)*(B y P Q*star (D₀ y P Q)).im)
def constant (y P Q c : ℝ) : ℝ :=
  Complex.normSq (N₀ y P Q)-(c^2/4)*Complex.normSq (D₀ y P Q)
def outside (d y P Q c : ℝ) : ℝ :=
  QuadraticDisk.outside (lead y P Q c) (bx y P Q c) (bt y P Q c) (r d y) (g d y)
def directed (d y P Q c : ℝ) : ℝ :=
  QuadraticDisk.directed (lead y P Q c) (bx y P Q c) (bt y P Q c)
    (constant y P Q c) (r d y) (g d y)
def reserve (d y P Q c : ℝ) : ℝ :=
  QuadraticDisk.reserve (lead y P Q c) (bx y P Q c) (bt y P Q c)
    (constant y P Q c) (r d y) (g d y)

theorem quadratic_identity (y P Q c : ℝ) (ζ : ℂ) :
    Complex.normSq (A P Q*ζ+N₀ y P Q)-(c^2/4)*Complex.normSq (B y P Q*ζ+D₀ y P Q) =
      QuadraticDisk.value (lead y P Q c) (bx y P Q c) (bt y P Q c) (constant y P Q c) ζ := by
  simp only [QuadraticDisk.value,lead,bx,bt,constant,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im]
  ring

theorem log_lower_of_signs (d y P Q c : ℝ) (hd : 0 ≤ d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q) (hc : c ∈ Ioc (0 : ℝ) (1/2))
    (hO : 0 ≤ outside d y P Q c) (hD : 0 ≤ directed d y P Q c)
    (hR : 0 ≤ reserve d y P Q c) (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) :
    Real.log (c/2) ≤ Real.log ‖quotient y P Q ζ‖ := by
  have ha : 0 < lead y P Q c :=
    TailHalfGeometry.tangent_lead_pos y P Q c hy hP hQ ⟨hc.1.le,hc.2⟩
  have hr : 0 ≤ r d y := by unfold r; positivity
  have hH := QuadraticDisk.convex_nonneg _ _ _ _ _ _ ha hr hO hD hR ζ hζ
  rw [← quadratic_identity] at hH
  have hb := Complex.normSq_pos.mpr (TailHalfGeometry.denominator_ne_zero d y P Q hy hP hQ ζ hζ)
  have hs : (c/2)^2 ≤ ‖quotient y P Q ζ‖^2 := by
    rw [quotient,norm_div,div_pow,← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    apply (le_div_iff₀ hb).mpr
    nlinarith only [hH]
  have hk : 0 < c/2 := by linarith only [hc.1]
  have hn := (sq_le_sq₀ hk.le (norm_nonneg (quotient y P Q ζ))).mp hs
  exact Real.log_le_log hk hn

theorem tangent_log_identity (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1/2)) :
    Real.log (c/2) = -Real.arsinh (2/(4*c/(1-c^2)))-Real.log 2 := by
  have hc0 : 0 < c := hc.1
  have hd : 0 < 1-c^2 := by
    have h := pow_le_pow_left₀ hc0.le hc.2 2
    nlinarith only [h]
  have hr : 2/(4*c/(1-c^2))=(1-c^2)/(2*c) := by
    field_simp [hc.1.ne',hd.ne']
  have hs : Real.sqrt (1+((1-c^2)/(2*c))^2)=(1+c^2)/(2*c) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    field_simp [hc.1.ne']
    ring
  rw [hr,Real.arsinh,hs,
    show (1-c^2)/(2*c)+(1+c^2)/(2*c)=1/c by field_simp; ring,
    Real.log_one_div,Real.log_div hc.1.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  ring

attribute [-instance] SimpleGraph.fintypeEdgeSetSup

theorem graph_lower_of_actual_signs {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (y c : ℝ)
    (hy : 0 < y) (hc : c ∈ Ioc (0 : ℝ) (1/2))
    (hO : 0 ≤ outside (C.degree u) y (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c)
    (hD : 0 ≤ directed (C.degree u) y (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c)
    (hR : 0 ≤ reserve (C.degree u) y (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c) :
    Real.log (c/2) ≤ MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  have hp := div_nonneg (PathEnclosure.arm_nonneg y p) hy.le
  have hq := div_nonneg (PathEnclosure.arm_nonneg y q) hy.le
  have h := log_lower_of_signs (C.degree u) y _ _ c (by positivity) hy
    (by linarith only [hp]) (by linarith only [hq]) hc hO hD hR _ (schur_in_disk C u y hy).1
  change Real.log (c/2) ≤ Real.log ‖(shifted (z y) (source C u p q)).det /
    (shifted (z y) (fused C u p q)).det‖
  rw [concrete_graph_quotient C u y hy p q]
  exact h

theorem tangent_graph_lower_of_actual_signs {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (y c : ℝ)
    (hy : 0 < y) (hc : c ∈ Ioc (0 : ℝ) (1/2))
    (hrelation : (C.degree u : ℝ)*y=4*c/(1-c^2))
    (hO : 0 ≤ outside (C.degree u) y (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c)
    (hD : 0 ≤ directed (C.degree u) y (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c)
    (hR : 0 ≤ reserve (C.degree u) y (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c) :
    -Real.arsinh (2/((C.degree u : ℝ)*y))-Real.log 2 ≤
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  rw [hrelation,← tangent_log_identity c hc]
  exact graph_lower_of_actual_signs C u p q y c hy hc hO hD hR

#print axioms quadratic_identity
#print axioms log_lower_of_signs
#print axioms tangent_log_identity
#print axioms graph_lower_of_actual_signs
#print axioms tangent_graph_lower_of_actual_signs
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.LowStripGeometry
