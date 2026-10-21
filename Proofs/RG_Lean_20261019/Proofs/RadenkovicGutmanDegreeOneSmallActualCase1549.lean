/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1549 : Family 9 := level9.get ⟨277,by decide⟩
def sourceMap1549 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,5,6,7,3,4] (sourceLabel 9 0 0 v)
def fusedMap1549 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,4,5,6,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1549_checked : acceptsGraphIso
    (source (graph core1549) (root 9) 0 0) DegreeOneSmallSpectrum697.graph sourceMap1549=true := by decide +kernel
theorem fusedMap1549_checked : acceptsGraphIso
    (fused (graph core1549) (root 9) 0 0) DegreeOneSmallSpectrum570.graph fusedMap1549=true := by decide +kernel
theorem certified1549 : Certified (graph core1549) (root 9) 0 0 :=
  of_native_maps core1549 DegreeOneSmallSpectrum697.graph DegreeOneSmallSpectrum570.graph
    sourceMap1549 fusedMap1549 sourceMap1549_checked fusedMap1549_checked
    DegreeOneSmallComparisons.comparison1549
#print axioms sourceMap1549_checked
#print axioms fusedMap1549_checked
#print axioms certified1549
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
