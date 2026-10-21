/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2448 : Family 10 := level10.get ⟨1421,by decide⟩
def sourceMap2448 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,10,11,12,1,2,3,4,8,9,6,7] (sourceLabel 10 0 0 v)
def fusedMap2448 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2448_checked : acceptsGraphIso
    (source (graph core2448) (root 10) 0 0) DegreeOneSmallSpectrum1606.graph sourceMap2448=true := by decide +kernel
theorem fusedMap2448_checked : acceptsGraphIso
    (fused (graph core2448) (root 10) 0 0) DegreeOneSmallSpectrum1979.graph fusedMap2448=true := by decide +kernel
theorem certified2448 : Certified (graph core2448) (root 10) 0 0 :=
  of_native_maps core2448 DegreeOneSmallSpectrum1606.graph DegreeOneSmallSpectrum1979.graph
    sourceMap2448 fusedMap2448 sourceMap2448_checked fusedMap2448_checked
    DegreeOneSmallComparisons.comparison2448
#print axioms sourceMap2448_checked
#print axioms fusedMap2448_checked
#print axioms certified2448
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
