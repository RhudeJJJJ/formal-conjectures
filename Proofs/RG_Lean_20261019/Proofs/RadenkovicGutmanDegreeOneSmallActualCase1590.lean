/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1590 : Family 9 := level9.get ⟨331,by decide⟩
def sourceMap1590 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1590 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1590_checked : acceptsGraphIso
    (source (graph core1590) (root 9) 0 1) DegreeOneSmallSpectrum1628.graph sourceMap1590=true := by decide +kernel
theorem fusedMap1590_checked : acceptsGraphIso
    (fused (graph core1590) (root 9) 0 1) DegreeOneSmallSpectrum1010.graph fusedMap1590=true := by decide +kernel
theorem certified1590 : Certified (graph core1590) (root 9) 0 1 :=
  of_native_maps core1590 DegreeOneSmallSpectrum1628.graph DegreeOneSmallSpectrum1010.graph
    sourceMap1590 fusedMap1590 sourceMap1590_checked fusedMap1590_checked
    DegreeOneSmallComparisons.comparison1590
#print axioms sourceMap1590_checked
#print axioms fusedMap1590_checked
#print axioms certified1590
def sourceMap1590swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1590swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1590swap_checked : acceptsGraphIso
    (source (graph core1590) (root 9) 1 0) DegreeOneSmallSpectrum1628.graph sourceMap1590swap=true := by decide +kernel
theorem fusedMap1590swap_checked : acceptsGraphIso
    (fused (graph core1590) (root 9) 1 0) DegreeOneSmallSpectrum1010.graph fusedMap1590swap=true := by decide +kernel
theorem certified1590swap : Certified (graph core1590) (root 9) 1 0 :=
  of_native_maps core1590 DegreeOneSmallSpectrum1628.graph DegreeOneSmallSpectrum1010.graph
    sourceMap1590swap fusedMap1590swap sourceMap1590swap_checked fusedMap1590swap_checked
    DegreeOneSmallComparisons.comparison1590
#print axioms sourceMap1590swap_checked
#print axioms fusedMap1590swap_checked
#print axioms certified1590swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
