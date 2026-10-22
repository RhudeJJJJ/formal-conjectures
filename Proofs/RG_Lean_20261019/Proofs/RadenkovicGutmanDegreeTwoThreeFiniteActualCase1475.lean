/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1475 : Family 10 := level10.get ⟨200,by decide⟩
def sourceMap1475 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1475 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1475_checked : acceptsGraphIso
    (source (graph core1475) (root 10) 0 2) DegreeTwoThreeSpectrum2470.graph sourceMap1475=true := by decide +kernel
theorem fusedMap1475_checked : acceptsGraphIso
    (fused (graph core1475) (root 10) 0 2) DegreeTwoThreeSpectrum2472.graph fusedMap1475=true := by decide +kernel
theorem certified1475 : Certified (graph core1475) (root 10) 0 2 :=
  of_native_maps core1475 DegreeTwoThreeSpectrum2470.graph DegreeTwoThreeSpectrum2472.graph
    sourceMap1475 fusedMap1475 sourceMap1475_checked fusedMap1475_checked
    DegreeTwoThreeFiniteComparisons.comparison1475
#print axioms sourceMap1475_checked
#print axioms fusedMap1475_checked
#print axioms certified1475
def sourceMap1475swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1475swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1475swap_checked : acceptsGraphIso
    (source (graph core1475) (root 10) 2 0) DegreeTwoThreeSpectrum2470.graph sourceMap1475swap=true := by decide +kernel
theorem fusedMap1475swap_checked : acceptsGraphIso
    (fused (graph core1475) (root 10) 2 0) DegreeTwoThreeSpectrum2472.graph fusedMap1475swap=true := by decide +kernel
theorem certified1475swap : Certified (graph core1475) (root 10) 2 0 :=
  of_native_maps core1475 DegreeTwoThreeSpectrum2470.graph DegreeTwoThreeSpectrum2472.graph
    sourceMap1475swap fusedMap1475swap sourceMap1475swap_checked fusedMap1475swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1475
#print axioms sourceMap1475swap_checked
#print axioms fusedMap1475swap_checked
#print axioms certified1475swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
