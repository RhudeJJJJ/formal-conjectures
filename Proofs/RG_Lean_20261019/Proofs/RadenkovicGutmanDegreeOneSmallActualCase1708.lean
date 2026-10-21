/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1708 : Family 9 := level9.get ⟨487,by decide⟩
def sourceMap1708 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1708 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1708_checked : acceptsGraphIso
    (source (graph core1708) (root 9) 0 1) DegreeOneSmallSpectrum1964.graph sourceMap1708=true := by decide +kernel
theorem fusedMap1708_checked : acceptsGraphIso
    (fused (graph core1708) (root 9) 0 1) DegreeOneSmallSpectrum1457.graph fusedMap1708=true := by decide +kernel
theorem certified1708 : Certified (graph core1708) (root 9) 0 1 :=
  of_native_maps core1708 DegreeOneSmallSpectrum1964.graph DegreeOneSmallSpectrum1457.graph
    sourceMap1708 fusedMap1708 sourceMap1708_checked fusedMap1708_checked
    DegreeOneSmallComparisons.comparison1708
#print axioms sourceMap1708_checked
#print axioms fusedMap1708_checked
#print axioms certified1708
def sourceMap1708swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1708swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1708swap_checked : acceptsGraphIso
    (source (graph core1708) (root 9) 1 0) DegreeOneSmallSpectrum1964.graph sourceMap1708swap=true := by decide +kernel
theorem fusedMap1708swap_checked : acceptsGraphIso
    (fused (graph core1708) (root 9) 1 0) DegreeOneSmallSpectrum1457.graph fusedMap1708swap=true := by decide +kernel
theorem certified1708swap : Certified (graph core1708) (root 9) 1 0 :=
  of_native_maps core1708 DegreeOneSmallSpectrum1964.graph DegreeOneSmallSpectrum1457.graph
    sourceMap1708swap fusedMap1708swap sourceMap1708swap_checked fusedMap1708swap_checked
    DegreeOneSmallComparisons.comparison1708
#print axioms sourceMap1708swap_checked
#print axioms fusedMap1708swap_checked
#print axioms certified1708swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
