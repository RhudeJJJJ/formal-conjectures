/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1816 : Family 10 := level10.get ⟨1170,by decide⟩
def sourceMap1816 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,14,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1816 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1816_checked : acceptsGraphIso
    (source (graph core1816) (root 10) 0 2) DegreeTwoThreeSpectrum3269.graph sourceMap1816=true := by decide +kernel
theorem fusedMap1816_checked : acceptsGraphIso
    (fused (graph core1816) (root 10) 0 2) DegreeTwoThreeSpectrum3278.graph fusedMap1816=true := by decide +kernel
theorem certified1816 : Certified (graph core1816) (root 10) 0 2 :=
  of_native_maps core1816 DegreeTwoThreeSpectrum3269.graph DegreeTwoThreeSpectrum3278.graph
    sourceMap1816 fusedMap1816 sourceMap1816_checked fusedMap1816_checked
    DegreeTwoThreeFiniteComparisons.comparison1816
#print axioms sourceMap1816_checked
#print axioms fusedMap1816_checked
#print axioms certified1816
def sourceMap1816swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9,14] (sourceLabel 10 2 0 v)
def fusedMap1816swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1816swap_checked : acceptsGraphIso
    (source (graph core1816) (root 10) 2 0) DegreeTwoThreeSpectrum3269.graph sourceMap1816swap=true := by decide +kernel
theorem fusedMap1816swap_checked : acceptsGraphIso
    (fused (graph core1816) (root 10) 2 0) DegreeTwoThreeSpectrum3278.graph fusedMap1816swap=true := by decide +kernel
theorem certified1816swap : Certified (graph core1816) (root 10) 2 0 :=
  of_native_maps core1816 DegreeTwoThreeSpectrum3269.graph DegreeTwoThreeSpectrum3278.graph
    sourceMap1816swap fusedMap1816swap sourceMap1816swap_checked fusedMap1816swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1816
#print axioms sourceMap1816swap_checked
#print axioms fusedMap1816swap_checked
#print axioms certified1816swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
