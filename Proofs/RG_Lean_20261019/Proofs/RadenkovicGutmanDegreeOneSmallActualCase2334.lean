/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2334 : Family 10 := level10.get ⟨1040,by decide⟩
def sourceMap2334 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2334 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2334_checked : acceptsGraphIso
    (source (graph core2334) (root 10) 0 0) DegreeOneSmallSpectrum1630.graph sourceMap2334=true := by decide +kernel
theorem fusedMap2334_checked : acceptsGraphIso
    (fused (graph core2334) (root 10) 0 0) DegreeOneSmallSpectrum1636.graph fusedMap2334=true := by decide +kernel
theorem certified2334 : Certified (graph core2334) (root 10) 0 0 :=
  of_native_maps core2334 DegreeOneSmallSpectrum1630.graph DegreeOneSmallSpectrum1636.graph
    sourceMap2334 fusedMap2334 sourceMap2334_checked fusedMap2334_checked
    DegreeOneSmallComparisons.comparison2334
#print axioms sourceMap2334_checked
#print axioms fusedMap2334_checked
#print axioms certified2334
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
