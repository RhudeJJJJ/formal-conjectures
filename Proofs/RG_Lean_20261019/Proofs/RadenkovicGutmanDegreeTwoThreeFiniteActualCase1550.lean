/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1550 : Family 10 := level10.get ⟨453,by decide⟩
def sourceMap1550 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1550 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1550_checked : acceptsGraphIso
    (source (graph core1550) (root 10) 0 2) DegreeTwoThreeSpectrum2854.graph sourceMap1550=true := by decide +kernel
theorem fusedMap1550_checked : acceptsGraphIso
    (fused (graph core1550) (root 10) 0 2) DegreeTwoThreeSpectrum2979.graph fusedMap1550=true := by decide +kernel
theorem certified1550 : Certified (graph core1550) (root 10) 0 2 :=
  of_native_maps core1550 DegreeTwoThreeSpectrum2854.graph DegreeTwoThreeSpectrum2979.graph
    sourceMap1550 fusedMap1550 sourceMap1550_checked fusedMap1550_checked
    DegreeTwoThreeFiniteComparisons.comparison1550
#print axioms sourceMap1550_checked
#print axioms fusedMap1550_checked
#print axioms certified1550
def sourceMap1550swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1550swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,6,7,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1550swap_checked : acceptsGraphIso
    (source (graph core1550) (root 10) 2 0) DegreeTwoThreeSpectrum2854.graph sourceMap1550swap=true := by decide +kernel
theorem fusedMap1550swap_checked : acceptsGraphIso
    (fused (graph core1550) (root 10) 2 0) DegreeTwoThreeSpectrum2979.graph fusedMap1550swap=true := by decide +kernel
theorem certified1550swap : Certified (graph core1550) (root 10) 2 0 :=
  of_native_maps core1550 DegreeTwoThreeSpectrum2854.graph DegreeTwoThreeSpectrum2979.graph
    sourceMap1550swap fusedMap1550swap sourceMap1550swap_checked fusedMap1550swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1550
#print axioms sourceMap1550swap_checked
#print axioms fusedMap1550swap_checked
#print axioms certified1550swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
