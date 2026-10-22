/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1634 : Family 10 := level10.get ⟨698,by decide⟩
def sourceMap1634 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1634 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1634_checked : acceptsGraphIso
    (source (graph core1634) (root 10) 0 2) DegreeTwoThreeSpectrum3414.graph sourceMap1634=true := by decide +kernel
theorem fusedMap1634_checked : acceptsGraphIso
    (fused (graph core1634) (root 10) 0 2) DegreeTwoThreeSpectrum2659.graph fusedMap1634=true := by decide +kernel
theorem certified1634 : Certified (graph core1634) (root 10) 0 2 :=
  of_native_maps core1634 DegreeTwoThreeSpectrum3414.graph DegreeTwoThreeSpectrum2659.graph
    sourceMap1634 fusedMap1634 sourceMap1634_checked fusedMap1634_checked
    DegreeTwoThreeFiniteComparisons.comparison1634
#print axioms sourceMap1634_checked
#print axioms fusedMap1634_checked
#print axioms certified1634
def sourceMap1634swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1634swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1634swap_checked : acceptsGraphIso
    (source (graph core1634) (root 10) 2 0) DegreeTwoThreeSpectrum3414.graph sourceMap1634swap=true := by decide +kernel
theorem fusedMap1634swap_checked : acceptsGraphIso
    (fused (graph core1634) (root 10) 2 0) DegreeTwoThreeSpectrum2659.graph fusedMap1634swap=true := by decide +kernel
theorem certified1634swap : Certified (graph core1634) (root 10) 2 0 :=
  of_native_maps core1634 DegreeTwoThreeSpectrum3414.graph DegreeTwoThreeSpectrum2659.graph
    sourceMap1634swap fusedMap1634swap sourceMap1634swap_checked fusedMap1634swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1634
#print axioms sourceMap1634swap_checked
#print axioms fusedMap1634swap_checked
#print axioms certified1634swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
