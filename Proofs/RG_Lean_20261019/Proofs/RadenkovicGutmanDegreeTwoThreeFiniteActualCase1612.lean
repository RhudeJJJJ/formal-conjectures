/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1612 : Family 10 := level10.get ⟨639,by decide⟩
def sourceMap1612 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1612 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1612_checked : acceptsGraphIso
    (source (graph core1612) (root 10) 0 2) DegreeTwoThreeSpectrum3332.graph sourceMap1612=true := by decide +kernel
theorem fusedMap1612_checked : acceptsGraphIso
    (fused (graph core1612) (root 10) 0 2) DegreeTwoThreeSpectrum2584.graph fusedMap1612=true := by decide +kernel
theorem certified1612 : Certified (graph core1612) (root 10) 0 2 :=
  of_native_maps core1612 DegreeTwoThreeSpectrum3332.graph DegreeTwoThreeSpectrum2584.graph
    sourceMap1612 fusedMap1612 sourceMap1612_checked fusedMap1612_checked
    DegreeTwoThreeFiniteComparisons.comparison1612
#print axioms sourceMap1612_checked
#print axioms fusedMap1612_checked
#print axioms certified1612
def sourceMap1612swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1612swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1612swap_checked : acceptsGraphIso
    (source (graph core1612) (root 10) 2 0) DegreeTwoThreeSpectrum3332.graph sourceMap1612swap=true := by decide +kernel
theorem fusedMap1612swap_checked : acceptsGraphIso
    (fused (graph core1612) (root 10) 2 0) DegreeTwoThreeSpectrum2584.graph fusedMap1612swap=true := by decide +kernel
theorem certified1612swap : Certified (graph core1612) (root 10) 2 0 :=
  of_native_maps core1612 DegreeTwoThreeSpectrum3332.graph DegreeTwoThreeSpectrum2584.graph
    sourceMap1612swap fusedMap1612swap sourceMap1612swap_checked fusedMap1612swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1612
#print axioms sourceMap1612swap_checked
#print axioms fusedMap1612swap_checked
#print axioms certified1612swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
