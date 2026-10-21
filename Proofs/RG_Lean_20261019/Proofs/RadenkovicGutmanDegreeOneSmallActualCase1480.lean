/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1480 : Family 9 := level9.get ⟨214,by decide⟩
def sourceMap1480 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 9 0 1 v)
def fusedMap1480 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1480_checked : acceptsGraphIso
    (source (graph core1480) (root 9) 0 1) DegreeOneSmallSpectrum1356.graph sourceMap1480=true := by decide +kernel
theorem fusedMap1480_checked : acceptsGraphIso
    (fused (graph core1480) (root 9) 0 1) DegreeOneSmallSpectrum1358.graph fusedMap1480=true := by decide +kernel
theorem certified1480 : Certified (graph core1480) (root 9) 0 1 :=
  of_native_maps core1480 DegreeOneSmallSpectrum1356.graph DegreeOneSmallSpectrum1358.graph
    sourceMap1480 fusedMap1480 sourceMap1480_checked fusedMap1480_checked
    DegreeOneSmallComparisons.comparison1480
#print axioms sourceMap1480_checked
#print axioms fusedMap1480_checked
#print axioms certified1480
def sourceMap1480swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 9 1 0 v)
def fusedMap1480swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1480swap_checked : acceptsGraphIso
    (source (graph core1480) (root 9) 1 0) DegreeOneSmallSpectrum1356.graph sourceMap1480swap=true := by decide +kernel
theorem fusedMap1480swap_checked : acceptsGraphIso
    (fused (graph core1480) (root 9) 1 0) DegreeOneSmallSpectrum1358.graph fusedMap1480swap=true := by decide +kernel
theorem certified1480swap : Certified (graph core1480) (root 9) 1 0 :=
  of_native_maps core1480 DegreeOneSmallSpectrum1356.graph DegreeOneSmallSpectrum1358.graph
    sourceMap1480swap fusedMap1480swap sourceMap1480swap_checked fusedMap1480swap_checked
    DegreeOneSmallComparisons.comparison1480
#print axioms sourceMap1480swap_checked
#print axioms fusedMap1480swap_checked
#print axioms certified1480swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
