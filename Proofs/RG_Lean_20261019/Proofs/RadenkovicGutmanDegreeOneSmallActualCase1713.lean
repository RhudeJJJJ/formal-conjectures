/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1713 : Family 9 := level9.get ⟨494,by decide⟩
def sourceMap1713 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,4,5,6,7,8,2,3] (sourceLabel 9 0 0 v)
def fusedMap1713 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1713_checked : acceptsGraphIso
    (source (graph core1713) (root 9) 0 0) DegreeOneSmallSpectrum673.graph sourceMap1713=true := by decide +kernel
theorem fusedMap1713_checked : acceptsGraphIso
    (fused (graph core1713) (root 9) 0 0) DegreeOneSmallSpectrum826.graph fusedMap1713=true := by decide +kernel
theorem certified1713 : Certified (graph core1713) (root 9) 0 0 :=
  of_native_maps core1713 DegreeOneSmallSpectrum673.graph DegreeOneSmallSpectrum826.graph
    sourceMap1713 fusedMap1713 sourceMap1713_checked fusedMap1713_checked
    DegreeOneSmallComparisons.comparison1713
#print axioms sourceMap1713_checked
#print axioms fusedMap1713_checked
#print axioms certified1713
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
