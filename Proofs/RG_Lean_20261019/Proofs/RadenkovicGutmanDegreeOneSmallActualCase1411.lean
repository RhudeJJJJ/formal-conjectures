/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1411 : Family 9 := level9.get ⟨156,by decide⟩
def sourceMap1411 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (sourceLabel 9 0 0 v)
def fusedMap1411 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1411_checked : acceptsGraphIso
    (source (graph core1411) (root 9) 0 0) DegreeOneSmallSpectrum679.graph sourceMap1411=true := by decide +kernel
theorem fusedMap1411_checked : acceptsGraphIso
    (fused (graph core1411) (root 9) 0 0) DegreeOneSmallSpectrum428.graph fusedMap1411=true := by decide +kernel
theorem certified1411 : Certified (graph core1411) (root 9) 0 0 :=
  of_native_maps core1411 DegreeOneSmallSpectrum679.graph DegreeOneSmallSpectrum428.graph
    sourceMap1411 fusedMap1411 sourceMap1411_checked fusedMap1411_checked
    DegreeOneSmallComparisons.comparison1411
#print axioms sourceMap1411_checked
#print axioms fusedMap1411_checked
#print axioms certified1411
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
