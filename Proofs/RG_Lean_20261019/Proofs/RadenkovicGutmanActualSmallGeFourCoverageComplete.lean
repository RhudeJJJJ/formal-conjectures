/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourCoverage00
import Proofs.RadenkovicGutmanActualSmallGeFourCoverage01
import Proofs.RadenkovicGutmanActualSmallGeFourCoverage02
import Proofs.RadenkovicGutmanActualSmallGeFourCoverage03
import Proofs.RadenkovicGutmanActualSmallGeFourCoverage04
import Proofs.RadenkovicGutmanActualSmallGeFourCoverage05
import Proofs.RadenkovicGutmanActualSmallGeFourCoverage06
import Proofs.RadenkovicGutmanActualSmallGeFourCoverage07
import Proofs.RadenkovicGutmanActualSmallGeFourCoverage08
import Proofs.RadenkovicGutmanActualSmallGeFourCoverage09
import Mathlib.Tactic.IntervalCases
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem parameter_coverage (n : ℕ) (hn : n≤9)
    (i : Fin (RootedCatalogueData.catalogue n).length) (p q : Fin 10)
    (h : eligible n i.val p.val q.val=true) :
    (⟨n,i.val,p.val,q.val⟩ : Key) ∈ keys := by
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
#print axioms parameter_coverage
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
