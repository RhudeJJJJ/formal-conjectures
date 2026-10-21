/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1650 : Family 9 := level9.get ⟨393,by decide⟩
def sourceMap1650 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,8,6,7] (sourceLabel 9 0 1 v)
def fusedMap1650 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1650_checked : acceptsGraphIso
    (source (graph core1650) (root 9) 0 1) DegreeOneSmallSpectrum1873.graph sourceMap1650=true := by decide +kernel
theorem fusedMap1650_checked : acceptsGraphIso
    (fused (graph core1650) (root 9) 0 1) DegreeOneSmallSpectrum1196.graph fusedMap1650=true := by decide +kernel
theorem certified1650 : Certified (graph core1650) (root 9) 0 1 :=
  of_native_maps core1650 DegreeOneSmallSpectrum1873.graph DegreeOneSmallSpectrum1196.graph
    sourceMap1650 fusedMap1650 sourceMap1650_checked fusedMap1650_checked
    DegreeOneSmallComparisons.comparison1650
#print axioms sourceMap1650_checked
#print axioms fusedMap1650_checked
#print axioms certified1650
def sourceMap1650swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,6,7,8] (sourceLabel 9 1 0 v)
def fusedMap1650swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1650swap_checked : acceptsGraphIso
    (source (graph core1650) (root 9) 1 0) DegreeOneSmallSpectrum1873.graph sourceMap1650swap=true := by decide +kernel
theorem fusedMap1650swap_checked : acceptsGraphIso
    (fused (graph core1650) (root 9) 1 0) DegreeOneSmallSpectrum1196.graph fusedMap1650swap=true := by decide +kernel
theorem certified1650swap : Certified (graph core1650) (root 9) 1 0 :=
  of_native_maps core1650 DegreeOneSmallSpectrum1873.graph DegreeOneSmallSpectrum1196.graph
    sourceMap1650swap fusedMap1650swap sourceMap1650swap_checked fusedMap1650swap_checked
    DegreeOneSmallComparisons.comparison1650
#print axioms sourceMap1650swap_checked
#print axioms fusedMap1650swap_checked
#print axioms certified1650swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
