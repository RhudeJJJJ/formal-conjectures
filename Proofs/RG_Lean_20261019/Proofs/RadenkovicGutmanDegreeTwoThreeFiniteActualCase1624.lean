/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1624 : Family 10 := level10.get ⟨670,by decide⟩
def sourceMap1624 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,14,7,8,9,13,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1624 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1624_checked : acceptsGraphIso
    (source (graph core1624) (root 10) 0 2) DegreeTwoThreeSpectrum3359.graph sourceMap1624=true := by decide +kernel
theorem fusedMap1624_checked : acceptsGraphIso
    (fused (graph core1624) (root 10) 0 2) DegreeTwoThreeSpectrum2622.graph fusedMap1624=true := by decide +kernel
theorem certified1624 : Certified (graph core1624) (root 10) 0 2 :=
  of_native_maps core1624 DegreeTwoThreeSpectrum3359.graph DegreeTwoThreeSpectrum2622.graph
    sourceMap1624 fusedMap1624 sourceMap1624_checked fusedMap1624_checked
    DegreeTwoThreeFiniteComparisons.comparison1624
#print axioms sourceMap1624_checked
#print axioms fusedMap1624_checked
#print axioms certified1624
def sourceMap1624swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,14,7,8,9,10,11,12,13] (sourceLabel 10 2 0 v)
def fusedMap1624swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1624swap_checked : acceptsGraphIso
    (source (graph core1624) (root 10) 2 0) DegreeTwoThreeSpectrum3359.graph sourceMap1624swap=true := by decide +kernel
theorem fusedMap1624swap_checked : acceptsGraphIso
    (fused (graph core1624) (root 10) 2 0) DegreeTwoThreeSpectrum2622.graph fusedMap1624swap=true := by decide +kernel
theorem certified1624swap : Certified (graph core1624) (root 10) 2 0 :=
  of_native_maps core1624 DegreeTwoThreeSpectrum3359.graph DegreeTwoThreeSpectrum2622.graph
    sourceMap1624swap fusedMap1624swap sourceMap1624swap_checked fusedMap1624swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1624
#print axioms sourceMap1624swap_checked
#print axioms fusedMap1624swap_checked
#print axioms certified1624swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
