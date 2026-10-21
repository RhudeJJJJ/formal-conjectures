/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1405 : Family 9 := level9.get ⟨149,by decide⟩
def sourceMap1405 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (sourceLabel 9 0 0 v)
def fusedMap1405 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1405_checked : acceptsGraphIso
    (source (graph core1405) (root 9) 0 0) DegreeOneSmallSpectrum663.graph sourceMap1405=true := by decide +kernel
theorem fusedMap1405_checked : acceptsGraphIso
    (fused (graph core1405) (root 9) 0 0) DegreeOneSmallSpectrum416.graph fusedMap1405=true := by decide +kernel
theorem certified1405 : Certified (graph core1405) (root 9) 0 0 :=
  of_native_maps core1405 DegreeOneSmallSpectrum663.graph DegreeOneSmallSpectrum416.graph
    sourceMap1405 fusedMap1405 sourceMap1405_checked fusedMap1405_checked
    DegreeOneSmallComparisons.comparison1405
#print axioms sourceMap1405_checked
#print axioms fusedMap1405_checked
#print axioms certified1405
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
