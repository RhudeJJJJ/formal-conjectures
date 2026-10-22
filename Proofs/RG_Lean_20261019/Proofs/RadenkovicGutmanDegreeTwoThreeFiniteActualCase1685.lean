/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1685 : Family 10 := level10.get ⟨842,by decide⟩
def sourceMap1685 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1685 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1685_checked : acceptsGraphIso
    (source (graph core1685) (root 10) 0 2) DegreeTwoThreeSpectrum3647.graph sourceMap1685=true := by decide +kernel
theorem fusedMap1685_checked : acceptsGraphIso
    (fused (graph core1685) (root 10) 0 2) DegreeTwoThreeSpectrum2828.graph fusedMap1685=true := by decide +kernel
theorem certified1685 : Certified (graph core1685) (root 10) 0 2 :=
  of_native_maps core1685 DegreeTwoThreeSpectrum3647.graph DegreeTwoThreeSpectrum2828.graph
    sourceMap1685 fusedMap1685 sourceMap1685_checked fusedMap1685_checked
    DegreeTwoThreeFiniteComparisons.comparison1685
#print axioms sourceMap1685_checked
#print axioms fusedMap1685_checked
#print axioms certified1685
def sourceMap1685swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1685swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1685swap_checked : acceptsGraphIso
    (source (graph core1685) (root 10) 2 0) DegreeTwoThreeSpectrum3647.graph sourceMap1685swap=true := by decide +kernel
theorem fusedMap1685swap_checked : acceptsGraphIso
    (fused (graph core1685) (root 10) 2 0) DegreeTwoThreeSpectrum2828.graph fusedMap1685swap=true := by decide +kernel
theorem certified1685swap : Certified (graph core1685) (root 10) 2 0 :=
  of_native_maps core1685 DegreeTwoThreeSpectrum3647.graph DegreeTwoThreeSpectrum2828.graph
    sourceMap1685swap fusedMap1685swap sourceMap1685swap_checked fusedMap1685swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1685
#print axioms sourceMap1685swap_checked
#print axioms fusedMap1685swap_checked
#print axioms certified1685swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
