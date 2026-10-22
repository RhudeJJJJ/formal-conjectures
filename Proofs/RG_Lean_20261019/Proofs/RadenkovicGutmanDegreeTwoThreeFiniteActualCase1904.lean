/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1904 : Family 10 := level10.get ⟨1379,by decide⟩
def sourceMap1904 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1904 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1904_checked : acceptsGraphIso
    (source (graph core1904) (root 10) 0 2) DegreeTwoThreeSpectrum3293.graph sourceMap1904=true := by decide +kernel
theorem fusedMap1904_checked : acceptsGraphIso
    (fused (graph core1904) (root 10) 0 2) DegreeTwoThreeSpectrum3584.graph fusedMap1904=true := by decide +kernel
theorem certified1904 : Certified (graph core1904) (root 10) 0 2 :=
  of_native_maps core1904 DegreeTwoThreeSpectrum3293.graph DegreeTwoThreeSpectrum3584.graph
    sourceMap1904 fusedMap1904 sourceMap1904_checked fusedMap1904_checked
    DegreeTwoThreeFiniteComparisons.comparison1904
#print axioms sourceMap1904_checked
#print axioms fusedMap1904_checked
#print axioms certified1904
def sourceMap1904swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1904swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1904swap_checked : acceptsGraphIso
    (source (graph core1904) (root 10) 2 0) DegreeTwoThreeSpectrum3293.graph sourceMap1904swap=true := by decide +kernel
theorem fusedMap1904swap_checked : acceptsGraphIso
    (fused (graph core1904) (root 10) 2 0) DegreeTwoThreeSpectrum3584.graph fusedMap1904swap=true := by decide +kernel
theorem certified1904swap : Certified (graph core1904) (root 10) 2 0 :=
  of_native_maps core1904 DegreeTwoThreeSpectrum3293.graph DegreeTwoThreeSpectrum3584.graph
    sourceMap1904swap fusedMap1904swap sourceMap1904swap_checked fusedMap1904swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1904
#print axioms sourceMap1904swap_checked
#print axioms fusedMap1904swap_checked
#print axioms certified1904swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
