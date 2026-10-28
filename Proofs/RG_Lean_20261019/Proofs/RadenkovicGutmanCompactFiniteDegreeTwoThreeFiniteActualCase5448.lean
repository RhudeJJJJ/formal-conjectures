/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5448 : Family 7 := level7.get ⟨92,by decide⟩
def sourceMap5448 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,6,7,8,9,1,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap5448 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,6,7,8,9,1,2,5,3,4] (fusedLabel 7 0 0 v)
theorem sourceMap5448_checked : acceptsGraphIso
    (source (graph core5448) (root 7) 0 0) SmallGeFourSpectrum021.graph sourceMap5448=true := by decide +kernel
theorem fusedMap5448_checked : acceptsGraphIso
    (fused (graph core5448) (root 7) 0 0) DegreeOneSmallSpectrum132.graph fusedMap5448=true := by decide +kernel
theorem certified5448 : Certified (graph core5448) (root 7) 0 0 :=
  of_native_maps core5448 SmallGeFourSpectrum021.graph DegreeOneSmallSpectrum132.graph
    sourceMap5448 fusedMap5448 sourceMap5448_checked fusedMap5448_checked
    DegreeTwoThreeFiniteComparisons.comparison5448
#print axioms sourceMap5448_checked
#print axioms fusedMap5448_checked
#print axioms certified5448
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
