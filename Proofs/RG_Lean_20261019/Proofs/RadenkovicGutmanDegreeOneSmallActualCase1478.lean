/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1478 : Family 9 := level9.get ⟨213,by decide⟩
def sourceMap1478 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1478 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1478_checked : acceptsGraphIso
    (source (graph core1478) (root 9) 0 1) DegreeOneSmallSpectrum1351.graph sourceMap1478=true := by decide +kernel
theorem fusedMap1478_checked : acceptsGraphIso
    (fused (graph core1478) (root 9) 0 1) DegreeOneSmallSpectrum1353.graph fusedMap1478=true := by decide +kernel
theorem certified1478 : Certified (graph core1478) (root 9) 0 1 :=
  of_native_maps core1478 DegreeOneSmallSpectrum1351.graph DegreeOneSmallSpectrum1353.graph
    sourceMap1478 fusedMap1478 sourceMap1478_checked fusedMap1478_checked
    DegreeOneSmallComparisons.comparison1478
#print axioms sourceMap1478_checked
#print axioms fusedMap1478_checked
#print axioms certified1478
def sourceMap1478swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1478swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1478swap_checked : acceptsGraphIso
    (source (graph core1478) (root 9) 1 0) DegreeOneSmallSpectrum1351.graph sourceMap1478swap=true := by decide +kernel
theorem fusedMap1478swap_checked : acceptsGraphIso
    (fused (graph core1478) (root 9) 1 0) DegreeOneSmallSpectrum1353.graph fusedMap1478swap=true := by decide +kernel
theorem certified1478swap : Certified (graph core1478) (root 9) 1 0 :=
  of_native_maps core1478 DegreeOneSmallSpectrum1351.graph DegreeOneSmallSpectrum1353.graph
    sourceMap1478swap fusedMap1478swap sourceMap1478swap_checked fusedMap1478swap_checked
    DegreeOneSmallComparisons.comparison1478
#print axioms sourceMap1478swap_checked
#print axioms fusedMap1478swap_checked
#print axioms certified1478swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
