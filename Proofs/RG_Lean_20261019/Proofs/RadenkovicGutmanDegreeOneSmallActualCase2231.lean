/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2231 : Family 10 := level10.get ⟨771,by decide⟩
def sourceMap2231 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2231 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2231_checked : acceptsGraphIso
    (source (graph core2231) (root 10) 0 0) DegreeOneSmallSpectrum1873.graph sourceMap2231=true := by decide +kernel
theorem fusedMap2231_checked : acceptsGraphIso
    (fused (graph core2231) (root 10) 0 0) DegreeOneSmallSpectrum1404.graph fusedMap2231=true := by decide +kernel
theorem certified2231 : Certified (graph core2231) (root 10) 0 0 :=
  of_native_maps core2231 DegreeOneSmallSpectrum1873.graph DegreeOneSmallSpectrum1404.graph
    sourceMap2231 fusedMap2231 sourceMap2231_checked fusedMap2231_checked
    DegreeOneSmallComparisons.comparison2231
#print axioms sourceMap2231_checked
#print axioms fusedMap2231_checked
#print axioms certified2231
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
