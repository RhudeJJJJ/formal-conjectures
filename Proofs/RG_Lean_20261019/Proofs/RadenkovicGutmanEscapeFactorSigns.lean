/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanCorrelatedEscapeReduction

/-! Exact factors of the unchanged concave escape quadratic. -/
namespace Gebendorfer.RadenkovicGutman.EscapeFactorSigns
open CorrelatedEscapeReduction
noncomputable section
set_option maxHeartbeats 0
def directedCore (d y P Q t : ℝ) : ℝ :=
  factorCore d y P Q t+Focus.r d y*factorVertical y P Q t+
    2*factorLead y P Q t*(Focus.r d y)^2
def reserveInner (d y P Q t : ℝ) : ℝ :=
  (factorCore d y P Q t)^2+2*factorCore d y P Q t*Focus.r d y*factorVertical y P Q t+
    (Focus.r d y)^2*(4*factorLead y P Q t*factorBase y P Q t-(factorHorizontal y P Q t)^2)
theorem directed_identity (d y P Q t : ℝ) :
    CorrelatedEscape.directed d y P Q t = 4*factorLead y P Q t*directedCore d y P Q t :=
  directed_reduced d y P Q t
theorem reserve_identity (d y P Q t : ℝ) :
    CorrelatedEscape.reserve d y P Q t = 16*(factorLead y P Q t)^2*reserveInner d y P Q t :=
  reserve_reduced d y P Q t
#print axioms directed_identity
#print axioms reserve_identity
end
end Gebendorfer.RadenkovicGutman.EscapeFactorSigns
