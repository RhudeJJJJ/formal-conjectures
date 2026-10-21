/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoverage00
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoverage01
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoverage02
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoverage03
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoverage04
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoverage05
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoverage06
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoverage07
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoverage08
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoverage09
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteCoverage10
import Mathlib.Tactic.IntervalCases
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem parameter_coverage (n : ℕ) (hn : n≤10)
    (i : Fin (RootedCatalogueData.catalogue n).length) (p q : Fin 13)
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
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
