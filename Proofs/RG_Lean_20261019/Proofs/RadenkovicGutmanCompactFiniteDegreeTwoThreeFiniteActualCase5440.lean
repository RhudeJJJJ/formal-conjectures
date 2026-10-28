/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5440 : Family 7 := level7.get ⟨49,by decide⟩
def sourceMap5440 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap5440 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,4,5,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap5440_checked : acceptsGraphIso
    (source (graph core5440) (root 7) 0 0) DegreeOneSmallSpectrum095.graph sourceMap5440=true := by decide +kernel
theorem fusedMap5440_checked : acceptsGraphIso
    (fused (graph core5440) (root 7) 0 0) DegreeOneSmallSpectrum141.graph fusedMap5440=true := by decide +kernel
theorem certified5440 : Certified (graph core5440) (root 7) 0 0 :=
  of_native_maps core5440 DegreeOneSmallSpectrum095.graph DegreeOneSmallSpectrum141.graph
    sourceMap5440 fusedMap5440 sourceMap5440_checked fusedMap5440_checked
    DegreeTwoThreeFiniteComparisons.comparison5440
#print axioms sourceMap5440_checked
#print axioms fusedMap5440_checked
#print axioms certified5440
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
