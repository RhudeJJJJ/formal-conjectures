/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanHighDegreeInputFromEscape
import Proofs.RadenkovicGutmanReducedEscapeSigns
import Proofs.RadenkovicGutmanOriginalAssembly

/-! Candidate assembly of the exact seventh original Input family.
The other six families remain separate obligations. -/
namespace Gebendorfer.RadenkovicGutman.OriginalDegreeGeFortysix
open CoreQuotient
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
attribute [-instance] SimpleGraph.fintypeEdgeSetSup

theorem normalized_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 46 ≤ C.degree u) :
    (2/47 : ℝ) < ActualFusionIntegral.normalizedIntegral C u p q 2 :=
  HighDegreeInputFromEscape.normalized_target_of_escape_signs C u p q hd
    (ReducedEscapeSigns.signs _ (by exact_mod_cast hd))

theorem input_family (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (_hT : (source C u p q).IsTree) (hd : 46 ≤ C.degree u) :
    (2/47 : ℝ) < ActualFusionIntegral.normalizedIntegral C u p q 2 :=
  normalized_lower C u p q hd

theorem strict_fusion {m : ℕ} (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : 46 ≤ C.degree u) :
    laplacianEnergy (fused C u p q) < laplacianEnergy (source C u p q) := by
  have hn := OriginalAssembly.source_order_ge_degree_add_three C u p q
  exact OriginalAssembly.strict_of_cutoff_reserve C u p q 47 hT (by omega)
    (by omega) (by omega) (normalized_lower C u p q hd)

#print axioms normalized_lower
#print axioms input_family
#print axioms strict_fusion
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.OriginalDegreeGeFortysix
