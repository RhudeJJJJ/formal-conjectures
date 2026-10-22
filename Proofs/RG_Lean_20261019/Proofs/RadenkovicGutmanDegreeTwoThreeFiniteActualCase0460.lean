/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0460 : Family 10 := level10.get ⟨266,by decide⟩
def sourceMap0460 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0460 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0460_checked : acceptsGraphIso
    (source (graph core0460) (root 10) 0 0) DegreeOneSmallSpectrum1046.graph sourceMap0460=true := by decide +kernel
theorem fusedMap0460_checked : acceptsGraphIso
    (fused (graph core0460) (root 10) 0 0) DegreeOneSmallSpectrum1273.graph fusedMap0460=true := by decide +kernel
theorem certified0460 : Certified (graph core0460) (root 10) 0 0 :=
  of_native_maps core0460 DegreeOneSmallSpectrum1046.graph DegreeOneSmallSpectrum1273.graph
    sourceMap0460 fusedMap0460 sourceMap0460_checked fusedMap0460_checked
    DegreeTwoThreeFiniteComparisons.comparison0460
#print axioms sourceMap0460_checked
#print axioms fusedMap0460_checked
#print axioms certified0460
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
