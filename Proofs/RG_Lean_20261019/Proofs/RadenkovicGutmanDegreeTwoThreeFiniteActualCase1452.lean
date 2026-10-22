/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1452 : Family 10 := level10.get ⟨116,by decide⟩
def sourceMap1452 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1452 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1452_checked : acceptsGraphIso
    (source (graph core1452) (root 10) 0 2) DegreeTwoThreeSpectrum2802.graph sourceMap1452=true := by decide +kernel
theorem fusedMap1452_checked : acceptsGraphIso
    (fused (graph core1452) (root 10) 0 2) DegreeTwoThreeSpectrum2377.graph fusedMap1452=true := by decide +kernel
theorem certified1452 : Certified (graph core1452) (root 10) 0 2 :=
  of_native_maps core1452 DegreeTwoThreeSpectrum2802.graph DegreeTwoThreeSpectrum2377.graph
    sourceMap1452 fusedMap1452 sourceMap1452_checked fusedMap1452_checked
    DegreeTwoThreeFiniteComparisons.comparison1452
#print axioms sourceMap1452_checked
#print axioms fusedMap1452_checked
#print axioms certified1452
def sourceMap1452swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1452swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1452swap_checked : acceptsGraphIso
    (source (graph core1452) (root 10) 2 0) DegreeTwoThreeSpectrum2802.graph sourceMap1452swap=true := by decide +kernel
theorem fusedMap1452swap_checked : acceptsGraphIso
    (fused (graph core1452) (root 10) 2 0) DegreeTwoThreeSpectrum2377.graph fusedMap1452swap=true := by decide +kernel
theorem certified1452swap : Certified (graph core1452) (root 10) 2 0 :=
  of_native_maps core1452 DegreeTwoThreeSpectrum2802.graph DegreeTwoThreeSpectrum2377.graph
    sourceMap1452swap fusedMap1452swap sourceMap1452swap_checked fusedMap1452swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1452
#print axioms sourceMap1452swap_checked
#print axioms fusedMap1452swap_checked
#print axioms certified1452swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
