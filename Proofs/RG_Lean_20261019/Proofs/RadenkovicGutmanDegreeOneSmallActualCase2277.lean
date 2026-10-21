/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2277 : Family 10 := level10.get ⟨876,by decide⟩
def sourceMap2277 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2277 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2277_checked : acceptsGraphIso
    (source (graph core2277) (root 10) 0 0) DegreeOneSmallSpectrum1838.graph sourceMap2277=true := by decide +kernel
theorem fusedMap2277_checked : acceptsGraphIso
    (fused (graph core2277) (root 10) 0 0) DegreeOneSmallSpectrum1493.graph fusedMap2277=true := by decide +kernel
theorem certified2277 : Certified (graph core2277) (root 10) 0 0 :=
  of_native_maps core2277 DegreeOneSmallSpectrum1838.graph DegreeOneSmallSpectrum1493.graph
    sourceMap2277 fusedMap2277 sourceMap2277_checked fusedMap2277_checked
    DegreeOneSmallComparisons.comparison2277
#print axioms sourceMap2277_checked
#print axioms fusedMap2277_checked
#print axioms certified2277
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
