/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1720 : Family 9 := level9.get ⟨501,by decide⟩
def sourceMap1720 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1720 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1720_checked : acceptsGraphIso
    (source (graph core1720) (root 9) 0 1) DegreeOneSmallSpectrum1970.graph sourceMap1720=true := by decide +kernel
theorem fusedMap1720_checked : acceptsGraphIso
    (fused (graph core1720) (root 9) 0 1) DegreeOneSmallSpectrum1479.graph fusedMap1720=true := by decide +kernel
theorem certified1720 : Certified (graph core1720) (root 9) 0 1 :=
  of_native_maps core1720 DegreeOneSmallSpectrum1970.graph DegreeOneSmallSpectrum1479.graph
    sourceMap1720 fusedMap1720 sourceMap1720_checked fusedMap1720_checked
    DegreeOneSmallComparisons.comparison1720
#print axioms sourceMap1720_checked
#print axioms fusedMap1720_checked
#print axioms certified1720
def sourceMap1720swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1720swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1720swap_checked : acceptsGraphIso
    (source (graph core1720) (root 9) 1 0) DegreeOneSmallSpectrum1970.graph sourceMap1720swap=true := by decide +kernel
theorem fusedMap1720swap_checked : acceptsGraphIso
    (fused (graph core1720) (root 9) 1 0) DegreeOneSmallSpectrum1479.graph fusedMap1720swap=true := by decide +kernel
theorem certified1720swap : Certified (graph core1720) (root 9) 1 0 :=
  of_native_maps core1720 DegreeOneSmallSpectrum1970.graph DegreeOneSmallSpectrum1479.graph
    sourceMap1720swap fusedMap1720swap sourceMap1720swap_checked fusedMap1720swap_checked
    DegreeOneSmallComparisons.comparison1720
#print axioms sourceMap1720swap_checked
#print axioms fusedMap1720swap_checked
#print axioms certified1720swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
