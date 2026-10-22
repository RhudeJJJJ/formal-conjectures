/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1643 : Family 10 := level10.get ⟨722,by decide⟩
def sourceMap1643 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1643 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1643_checked : acceptsGraphIso
    (source (graph core1643) (root 10) 0 2) DegreeTwoThreeSpectrum3450.graph sourceMap1643=true := by decide +kernel
theorem fusedMap1643_checked : acceptsGraphIso
    (fused (graph core1643) (root 10) 0 2) DegreeTwoThreeSpectrum2686.graph fusedMap1643=true := by decide +kernel
theorem certified1643 : Certified (graph core1643) (root 10) 0 2 :=
  of_native_maps core1643 DegreeTwoThreeSpectrum3450.graph DegreeTwoThreeSpectrum2686.graph
    sourceMap1643 fusedMap1643 sourceMap1643_checked fusedMap1643_checked
    DegreeTwoThreeFiniteComparisons.comparison1643
#print axioms sourceMap1643_checked
#print axioms fusedMap1643_checked
#print axioms certified1643
def sourceMap1643swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1643swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1643swap_checked : acceptsGraphIso
    (source (graph core1643) (root 10) 2 0) DegreeTwoThreeSpectrum3450.graph sourceMap1643swap=true := by decide +kernel
theorem fusedMap1643swap_checked : acceptsGraphIso
    (fused (graph core1643) (root 10) 2 0) DegreeTwoThreeSpectrum2686.graph fusedMap1643swap=true := by decide +kernel
theorem certified1643swap : Certified (graph core1643) (root 10) 2 0 :=
  of_native_maps core1643 DegreeTwoThreeSpectrum3450.graph DegreeTwoThreeSpectrum2686.graph
    sourceMap1643swap fusedMap1643swap sourceMap1643swap_checked fusedMap1643swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1643
#print axioms sourceMap1643swap_checked
#print axioms fusedMap1643swap_checked
#print axioms certified1643swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
