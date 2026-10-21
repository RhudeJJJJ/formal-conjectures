/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2101 : Family 10 := level10.get ⟨521,by decide⟩
def sourceMap2101 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2101 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2101_checked : acceptsGraphIso
    (source (graph core2101) (root 10) 0 0) DegreeOneSmallSpectrum1643.graph sourceMap2101=true := by decide +kernel
theorem fusedMap2101_checked : acceptsGraphIso
    (fused (graph core2101) (root 10) 0 0) DegreeOneSmallSpectrum1016.graph fusedMap2101=true := by decide +kernel
theorem certified2101 : Certified (graph core2101) (root 10) 0 0 :=
  of_native_maps core2101 DegreeOneSmallSpectrum1643.graph DegreeOneSmallSpectrum1016.graph
    sourceMap2101 fusedMap2101 sourceMap2101_checked fusedMap2101_checked
    DegreeOneSmallComparisons.comparison2101
#print axioms sourceMap2101_checked
#print axioms fusedMap2101_checked
#print axioms certified2101
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
