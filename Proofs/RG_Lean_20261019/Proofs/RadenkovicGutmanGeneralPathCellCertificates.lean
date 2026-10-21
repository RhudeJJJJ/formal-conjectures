/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanGeneralPathPolynomials
import Proofs.RadenkovicGutmanRationalMobiusPolynomials
import Proofs.RadenkovicGutmanClassCellCertificates

namespace Gebendorfer.RadenkovicGutman.GeneralPathCellCertificates
open CoreQuotient PolynomialPathMap RationalComplexPolynomial
noncomputable section
set_option maxHeartbeats 0

/-- Source-bound rational coefficient identities, separation and common-basis
checks give a logarithmic payment for the actual two Laplace matrices. -/
theorem actual_log_lower {J : Type} [Fintype J]
    (x : ℚ) (y : ℝ) (hy : 0 < y) (p q : ℕ)
    (as bs cs es us vs js ns sep : List ℚ)
    (hpath : GeneralPathPolynomials.accepts x p q as bs cs es=true)
    (hpoly : RationalMobiusPolynomials.accepts as bs cs es us vs js ns sep=true)
    (cu cv cj : J → ℚ) (s L R : ℚ) (k n : ℕ)
    (hcoeff : ClassCellCertificates.accepts cu cv cj s L=true)
    (hlog : RationalLog.accepts L R k n=true)
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hu : realEvaluator y (ofList us)=∑ j, (cu j : ℝ)*w j)
    (hv : realEvaluator y (ofList vs)=∑ j, (cv j : ℝ)*w j)
    (hj : realEvaluator y (ofList js)=∑ j, (cj j : ℝ)*w j)
    (hn : 0 < realEvaluator y (ofList ns))
    (he : 0 < realEvaluator y (ofList sep))
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (hd : C.degree u=1) :
    (R : ℝ) ≤ MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) x y := by
  obtain ⟨ha,hb,hc,heval⟩ := GeneralPathPolynomials.accepts_sound x p q as bs cs es hpath y
  obtain ⟨huv,hvv,hjv,hnv,hev⟩ :=
    RationalMobiusPolynomials.accepts_sound as bs cs es us vs js ns sep hpoly y
  rw [hb,heval,ha,hc] at huv
  rw [ha,heval,hb,hc] at hvv
  rw [hb,ha] at hjv
  rw [hb,ha] at hnv
  rw [heval,hc] at hev
  rw [hnv] at hn
  rw [hev] at he
  have hs : (0 : ℝ) < s := by exact_mod_cast (of_decide_eq_true hcoeff).1
  have hbound := ClassCellCertificates.coefficient_sound cu cv cj s L hcoeff w hw _ _ _
    (huv.symm.trans hu) (hvv.symm.trans hv) (hjv.symm.trans hj)
  have hnorm := GeneralScaledQuotient.actual_norm_certificate C u hd x y hy p q s L hs he hn hbound
  exact ClassCellCertificates.log_lower_of_square L R k n hlog _ hnorm

#print axioms actual_log_lower
end
end Gebendorfer.RadenkovicGutman.GeneralPathCellCertificates
