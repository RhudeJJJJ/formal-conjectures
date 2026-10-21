/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2168 : Family 10 := level10.get ⟨637,by decide⟩
def sourceMap2168 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2168 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2168_checked : acceptsGraphIso
    (source (graph core2168) (root 10) 0 0) DegreeOneSmallSpectrum1797.graph sourceMap2168=true := by decide +kernel
theorem fusedMap2168_checked : acceptsGraphIso
    (fused (graph core2168) (root 10) 0 0) DegreeOneSmallSpectrum1224.graph fusedMap2168=true := by decide +kernel
theorem certified2168 : Certified (graph core2168) (root 10) 0 0 :=
  of_native_maps core2168 DegreeOneSmallSpectrum1797.graph DegreeOneSmallSpectrum1224.graph
    sourceMap2168 fusedMap2168 sourceMap2168_checked fusedMap2168_checked
    DegreeOneSmallComparisons.comparison2168
#print axioms sourceMap2168_checked
#print axioms fusedMap2168_checked
#print axioms certified2168
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
