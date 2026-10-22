/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1321 : Family 9 := level9.get ⟨407,by decide⟩
def sourceMap1321 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,8,5,6,7] (sourceLabel 9 0 2 v)
def fusedMap1321 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 0 2 v)
theorem sourceMap1321_checked : acceptsGraphIso
    (source (graph core1321) (root 9) 0 2) DegreeTwoThreeSpectrum2039.graph sourceMap1321=true := by decide +kernel
theorem fusedMap1321_checked : acceptsGraphIso
    (fused (graph core1321) (root 9) 0 2) DegreeTwoThreeSpectrum2075.graph fusedMap1321=true := by decide +kernel
theorem certified1321 : Certified (graph core1321) (root 9) 0 2 :=
  of_native_maps core1321 DegreeTwoThreeSpectrum2039.graph DegreeTwoThreeSpectrum2075.graph
    sourceMap1321 fusedMap1321 sourceMap1321_checked fusedMap1321_checked
    DegreeTwoThreeFiniteComparisons.comparison1321
#print axioms sourceMap1321_checked
#print axioms fusedMap1321_checked
#print axioms certified1321
def sourceMap1321swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,9,10,11,12,13,1,2,3,4,5,6,7,8] (sourceLabel 9 2 0 v)
def fusedMap1321swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 2 0 v)
theorem sourceMap1321swap_checked : acceptsGraphIso
    (source (graph core1321) (root 9) 2 0) DegreeTwoThreeSpectrum2039.graph sourceMap1321swap=true := by decide +kernel
theorem fusedMap1321swap_checked : acceptsGraphIso
    (fused (graph core1321) (root 9) 2 0) DegreeTwoThreeSpectrum2075.graph fusedMap1321swap=true := by decide +kernel
theorem certified1321swap : Certified (graph core1321) (root 9) 2 0 :=
  of_native_maps core1321 DegreeTwoThreeSpectrum2039.graph DegreeTwoThreeSpectrum2075.graph
    sourceMap1321swap fusedMap1321swap sourceMap1321swap_checked fusedMap1321swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1321
#print axioms sourceMap1321swap_checked
#print axioms fusedMap1321swap_checked
#print axioms certified1321swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
