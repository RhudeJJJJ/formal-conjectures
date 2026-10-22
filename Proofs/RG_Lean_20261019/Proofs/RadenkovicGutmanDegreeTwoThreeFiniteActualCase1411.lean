/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1411 : Family 9 := level9.get ⟨631,by decide⟩
def sourceMap1411 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1411 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1411_checked : acceptsGraphIso
    (source (graph core1411) (root 9) 0 2) DegreeTwoThreeSpectrum2286.graph sourceMap1411=true := by decide +kernel
theorem fusedMap1411_checked : acceptsGraphIso
    (fused (graph core1411) (root 9) 0 2) DegreeTwoThreeSpectrum2079.graph fusedMap1411=true := by decide +kernel
theorem certified1411 : Certified (graph core1411) (root 9) 0 2 :=
  of_native_maps core1411 DegreeTwoThreeSpectrum2286.graph DegreeTwoThreeSpectrum2079.graph
    sourceMap1411 fusedMap1411 sourceMap1411_checked fusedMap1411_checked
    DegreeTwoThreeFiniteComparisons.comparison1411
#print axioms sourceMap1411_checked
#print axioms fusedMap1411_checked
#print axioms certified1411
def sourceMap1411swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1411swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1411swap_checked : acceptsGraphIso
    (source (graph core1411) (root 9) 2 0) DegreeTwoThreeSpectrum2286.graph sourceMap1411swap=true := by decide +kernel
theorem fusedMap1411swap_checked : acceptsGraphIso
    (fused (graph core1411) (root 9) 2 0) DegreeTwoThreeSpectrum2079.graph fusedMap1411swap=true := by decide +kernel
theorem certified1411swap : Certified (graph core1411) (root 9) 2 0 :=
  of_native_maps core1411 DegreeTwoThreeSpectrum2286.graph DegreeTwoThreeSpectrum2079.graph
    sourceMap1411swap fusedMap1411swap sourceMap1411swap_checked fusedMap1411swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1411
#print axioms sourceMap1411swap_checked
#print axioms fusedMap1411swap_checked
#print axioms certified1411swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
