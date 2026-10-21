/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2268 : Family 10 := level10.get ⟨855,by decide⟩
def sourceMap2268 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2268 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2268_checked : acceptsGraphIso
    (source (graph core2268) (root 10) 0 0) DegreeOneSmallSpectrum1883.graph sourceMap2268=true := by decide +kernel
theorem fusedMap2268_checked : acceptsGraphIso
    (fused (graph core2268) (root 10) 0 0) DegreeOneSmallSpectrum1479.graph fusedMap2268=true := by decide +kernel
theorem certified2268 : Certified (graph core2268) (root 10) 0 0 :=
  of_native_maps core2268 DegreeOneSmallSpectrum1883.graph DegreeOneSmallSpectrum1479.graph
    sourceMap2268 fusedMap2268 sourceMap2268_checked fusedMap2268_checked
    DegreeOneSmallComparisons.comparison2268
#print axioms sourceMap2268_checked
#print axioms fusedMap2268_checked
#print axioms certified2268
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
