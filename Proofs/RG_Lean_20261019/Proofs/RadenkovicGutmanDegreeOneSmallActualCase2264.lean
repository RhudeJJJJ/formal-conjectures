/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2264 : Family 10 := level10.get ⟨847,by decide⟩
def sourceMap2264 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2264 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2264_checked : acceptsGraphIso
    (source (graph core2264) (root 10) 0 0) DegreeOneSmallSpectrum1771.graph sourceMap2264=true := by decide +kernel
theorem fusedMap2264_checked : acceptsGraphIso
    (fused (graph core2264) (root 10) 0 0) DegreeOneSmallSpectrum1472.graph fusedMap2264=true := by decide +kernel
theorem certified2264 : Certified (graph core2264) (root 10) 0 0 :=
  of_native_maps core2264 DegreeOneSmallSpectrum1771.graph DegreeOneSmallSpectrum1472.graph
    sourceMap2264 fusedMap2264 sourceMap2264_checked fusedMap2264_checked
    DegreeOneSmallComparisons.comparison2264
#print axioms sourceMap2264_checked
#print axioms fusedMap2264_checked
#print axioms certified2264
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
