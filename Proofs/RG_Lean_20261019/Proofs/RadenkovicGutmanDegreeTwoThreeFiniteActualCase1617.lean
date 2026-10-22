/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1617 : Family 10 := level10.get ⟨650,by decide⟩
def sourceMap1617 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1617 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1617_checked : acceptsGraphIso
    (source (graph core1617) (root 10) 0 2) DegreeTwoThreeSpectrum3340.graph sourceMap1617=true := by decide +kernel
theorem fusedMap1617_checked : acceptsGraphIso
    (fused (graph core1617) (root 10) 0 2) DegreeTwoThreeSpectrum2598.graph fusedMap1617=true := by decide +kernel
theorem certified1617 : Certified (graph core1617) (root 10) 0 2 :=
  of_native_maps core1617 DegreeTwoThreeSpectrum3340.graph DegreeTwoThreeSpectrum2598.graph
    sourceMap1617 fusedMap1617 sourceMap1617_checked fusedMap1617_checked
    DegreeTwoThreeFiniteComparisons.comparison1617
#print axioms sourceMap1617_checked
#print axioms fusedMap1617_checked
#print axioms certified1617
def sourceMap1617swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1617swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1617swap_checked : acceptsGraphIso
    (source (graph core1617) (root 10) 2 0) DegreeTwoThreeSpectrum3340.graph sourceMap1617swap=true := by decide +kernel
theorem fusedMap1617swap_checked : acceptsGraphIso
    (fused (graph core1617) (root 10) 2 0) DegreeTwoThreeSpectrum2598.graph fusedMap1617swap=true := by decide +kernel
theorem certified1617swap : Certified (graph core1617) (root 10) 2 0 :=
  of_native_maps core1617 DegreeTwoThreeSpectrum3340.graph DegreeTwoThreeSpectrum2598.graph
    sourceMap1617swap fusedMap1617swap sourceMap1617swap_checked fusedMap1617swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1617
#print axioms sourceMap1617swap_checked
#print axioms fusedMap1617swap_checked
#print axioms certified1617swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
