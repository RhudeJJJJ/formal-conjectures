/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1603 : Family 10 := level10.get ⟨611,by decide⟩
def sourceMap1603 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1603 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1603_checked : acceptsGraphIso
    (source (graph core1603) (root 10) 0 2) DegreeTwoThreeSpectrum3268.graph sourceMap1603=true := by decide +kernel
theorem fusedMap1603_checked : acceptsGraphIso
    (fused (graph core1603) (root 10) 0 2) DegreeTwoThreeSpectrum2556.graph fusedMap1603=true := by decide +kernel
theorem certified1603 : Certified (graph core1603) (root 10) 0 2 :=
  of_native_maps core1603 DegreeTwoThreeSpectrum3268.graph DegreeTwoThreeSpectrum2556.graph
    sourceMap1603 fusedMap1603 sourceMap1603_checked fusedMap1603_checked
    DegreeTwoThreeFiniteComparisons.comparison1603
#print axioms sourceMap1603_checked
#print axioms fusedMap1603_checked
#print axioms certified1603
def sourceMap1603swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1603swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1603swap_checked : acceptsGraphIso
    (source (graph core1603) (root 10) 2 0) DegreeTwoThreeSpectrum3268.graph sourceMap1603swap=true := by decide +kernel
theorem fusedMap1603swap_checked : acceptsGraphIso
    (fused (graph core1603) (root 10) 2 0) DegreeTwoThreeSpectrum2556.graph fusedMap1603swap=true := by decide +kernel
theorem certified1603swap : Certified (graph core1603) (root 10) 2 0 :=
  of_native_maps core1603 DegreeTwoThreeSpectrum3268.graph DegreeTwoThreeSpectrum2556.graph
    sourceMap1603swap fusedMap1603swap sourceMap1603swap_checked fusedMap1603swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1603
#print axioms sourceMap1603swap_checked
#print axioms fusedMap1603swap_checked
#print axioms certified1603swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
