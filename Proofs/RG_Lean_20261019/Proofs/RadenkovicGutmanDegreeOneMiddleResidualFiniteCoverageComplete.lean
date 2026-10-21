/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverage00
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverage01
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverage02
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverage03
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverage04
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverage05
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverage06
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverage07
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverage08
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverage09
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteCoverage10
import Mathlib.Tactic.IntervalCases
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem parameter_coverage (n : ℕ) (hn : n ≤ 10)
    (i : Fin (RootedCatalogueData.catalogue n).length) (p q : Fin 5)
    (h : eligible n i.val p.val q.val=true) : (⟨n,i.val,p.val,q.val⟩ : Key) ∈ keys := by
  interval_cases n
  · exact of_decide_eq_true covered0 i p q h
  · exact of_decide_eq_true covered1 i p q h
  · exact of_decide_eq_true covered2 i p q h
  · exact of_decide_eq_true covered3 i p q h
  · exact of_decide_eq_true covered4 i p q h
  · exact of_decide_eq_true covered5 i p q h
  · exact of_decide_eq_true covered6 i p q h
  · exact of_decide_eq_true covered7 i p q h
  · exact of_decide_eq_true covered8 i p q h
  · exact of_decide_eq_true covered9 i p q h
  · exact of_decide_eq_true covered10 i p q h
#print axioms parameter_coverage
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
