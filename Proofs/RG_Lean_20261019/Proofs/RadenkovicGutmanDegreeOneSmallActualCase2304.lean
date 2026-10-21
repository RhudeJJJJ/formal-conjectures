/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2304 : Family 10 := level10.get ⟨943,by decide⟩
def sourceMap2304 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,10,11,12,5,6,7,8,9,3,4] (sourceLabel 10 0 0 v)
def fusedMap2304 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2304_checked : acceptsGraphIso
    (source (graph core2304) (root 10) 0 0) DegreeOneSmallSpectrum1701.graph sourceMap2304=true := by decide +kernel
theorem fusedMap2304_checked : acceptsGraphIso
    (fused (graph core2304) (root 10) 0 0) DegreeOneSmallSpectrum1468.graph fusedMap2304=true := by decide +kernel
theorem certified2304 : Certified (graph core2304) (root 10) 0 0 :=
  of_native_maps core2304 DegreeOneSmallSpectrum1701.graph DegreeOneSmallSpectrum1468.graph
    sourceMap2304 fusedMap2304 sourceMap2304_checked fusedMap2304_checked
    DegreeOneSmallComparisons.comparison2304
#print axioms sourceMap2304_checked
#print axioms fusedMap2304_checked
#print axioms certified2304
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
