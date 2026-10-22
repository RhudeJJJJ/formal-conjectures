/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1622 : Family 10 := level10.get ⟨667,by decide⟩
def sourceMap1622 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,11,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1622 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1622_checked : acceptsGraphIso
    (source (graph core1622) (root 10) 0 2) DegreeTwoThreeSpectrum3368.graph sourceMap1622=true := by decide +kernel
theorem fusedMap1622_checked : acceptsGraphIso
    (fused (graph core1622) (root 10) 0 2) DegreeTwoThreeSpectrum2615.graph fusedMap1622=true := by decide +kernel
theorem certified1622 : Certified (graph core1622) (root 10) 0 2 :=
  of_native_maps core1622 DegreeTwoThreeSpectrum3368.graph DegreeTwoThreeSpectrum2615.graph
    sourceMap1622 fusedMap1622 sourceMap1622_checked fusedMap1622_checked
    DegreeTwoThreeFiniteComparisons.comparison1622
#print axioms sourceMap1622_checked
#print axioms fusedMap1622_checked
#print axioms certified1622
def sourceMap1622swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,7,8,9,11] (sourceLabel 10 2 0 v)
def fusedMap1622swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1622swap_checked : acceptsGraphIso
    (source (graph core1622) (root 10) 2 0) DegreeTwoThreeSpectrum3368.graph sourceMap1622swap=true := by decide +kernel
theorem fusedMap1622swap_checked : acceptsGraphIso
    (fused (graph core1622) (root 10) 2 0) DegreeTwoThreeSpectrum2615.graph fusedMap1622swap=true := by decide +kernel
theorem certified1622swap : Certified (graph core1622) (root 10) 2 0 :=
  of_native_maps core1622 DegreeTwoThreeSpectrum3368.graph DegreeTwoThreeSpectrum2615.graph
    sourceMap1622swap fusedMap1622swap sourceMap1622swap_checked fusedMap1622swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1622
#print axioms sourceMap1622swap_checked
#print axioms fusedMap1622swap_checked
#print axioms certified1622swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
