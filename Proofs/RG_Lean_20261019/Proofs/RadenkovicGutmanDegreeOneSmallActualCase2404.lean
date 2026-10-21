/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2404 : Family 10 := level10.get ⟨1253,by decide⟩
def sourceMap2404 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,4,5,2,3] (sourceLabel 10 0 0 v)
def fusedMap2404 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2404_checked : acceptsGraphIso
    (source (graph core2404) (root 10) 0 0) DegreeOneSmallSpectrum1799.graph sourceMap2404=true := by decide +kernel
theorem fusedMap2404_checked : acceptsGraphIso
    (fused (graph core2404) (root 10) 0 0) DegreeOneSmallSpectrum1907.graph fusedMap2404=true := by decide +kernel
theorem certified2404 : Certified (graph core2404) (root 10) 0 0 :=
  of_native_maps core2404 DegreeOneSmallSpectrum1799.graph DegreeOneSmallSpectrum1907.graph
    sourceMap2404 fusedMap2404 sourceMap2404_checked fusedMap2404_checked
    DegreeOneSmallComparisons.comparison2404
#print axioms sourceMap2404_checked
#print axioms fusedMap2404_checked
#print axioms certified2404
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
