/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1341 : Family 9 := level9.get ⟨96,by decide⟩
def sourceMap1341 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1341 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1341_checked : acceptsGraphIso
    (source (graph core1341) (root 9) 0 0) DegreeOneSmallSpectrum476.graph sourceMap1341=true := by decide +kernel
theorem fusedMap1341_checked : acceptsGraphIso
    (fused (graph core1341) (root 9) 0 0) DegreeOneSmallSpectrum575.graph fusedMap1341=true := by decide +kernel
theorem certified1341 : Certified (graph core1341) (root 9) 0 0 :=
  of_native_maps core1341 DegreeOneSmallSpectrum476.graph DegreeOneSmallSpectrum575.graph
    sourceMap1341 fusedMap1341 sourceMap1341_checked fusedMap1341_checked
    DegreeOneSmallComparisons.comparison1341
#print axioms sourceMap1341_checked
#print axioms fusedMap1341_checked
#print axioms certified1341
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
