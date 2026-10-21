/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1467 : Family 9 := level9.get ⟨204,by decide⟩
def sourceMap1467 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1467 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1467_checked : acceptsGraphIso
    (source (graph core1467) (root 9) 0 0) DegreeOneSmallSpectrum754.graph sourceMap1467=true := by decide +kernel
theorem fusedMap1467_checked : acceptsGraphIso
    (fused (graph core1467) (root 9) 0 0) DegreeOneSmallSpectrum506.graph fusedMap1467=true := by decide +kernel
theorem certified1467 : Certified (graph core1467) (root 9) 0 0 :=
  of_native_maps core1467 DegreeOneSmallSpectrum754.graph DegreeOneSmallSpectrum506.graph
    sourceMap1467 fusedMap1467 sourceMap1467_checked fusedMap1467_checked
    DegreeOneSmallComparisons.comparison1467
#print axioms sourceMap1467_checked
#print axioms fusedMap1467_checked
#print axioms certified1467
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
