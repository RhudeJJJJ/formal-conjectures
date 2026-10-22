/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1483 : Family 10 := level10.get ⟨234,by decide⟩
def sourceMap1483 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1483 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1483_checked : acceptsGraphIso
    (source (graph core1483) (root 10) 0 2) DegreeTwoThreeSpectrum2550.graph sourceMap1483=true := by decide +kernel
theorem fusedMap1483_checked : acceptsGraphIso
    (fused (graph core1483) (root 10) 0 2) DegreeTwoThreeSpectrum2552.graph fusedMap1483=true := by decide +kernel
theorem certified1483 : Certified (graph core1483) (root 10) 0 2 :=
  of_native_maps core1483 DegreeTwoThreeSpectrum2550.graph DegreeTwoThreeSpectrum2552.graph
    sourceMap1483 fusedMap1483 sourceMap1483_checked fusedMap1483_checked
    DegreeTwoThreeFiniteComparisons.comparison1483
#print axioms sourceMap1483_checked
#print axioms fusedMap1483_checked
#print axioms certified1483
def sourceMap1483swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1483swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1483swap_checked : acceptsGraphIso
    (source (graph core1483) (root 10) 2 0) DegreeTwoThreeSpectrum2550.graph sourceMap1483swap=true := by decide +kernel
theorem fusedMap1483swap_checked : acceptsGraphIso
    (fused (graph core1483) (root 10) 2 0) DegreeTwoThreeSpectrum2552.graph fusedMap1483swap=true := by decide +kernel
theorem certified1483swap : Certified (graph core1483) (root 10) 2 0 :=
  of_native_maps core1483 DegreeTwoThreeSpectrum2550.graph DegreeTwoThreeSpectrum2552.graph
    sourceMap1483swap fusedMap1483swap sourceMap1483swap_checked fusedMap1483swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1483
#print axioms sourceMap1483swap_checked
#print axioms fusedMap1483swap_checked
#print axioms certified1483swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
