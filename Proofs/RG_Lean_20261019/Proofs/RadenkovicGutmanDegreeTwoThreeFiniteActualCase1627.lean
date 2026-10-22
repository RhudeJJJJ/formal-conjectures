/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1627 : Family 10 := level10.get ⟨675,by decide⟩
def sourceMap1627 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1627 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1627_checked : acceptsGraphIso
    (source (graph core1627) (root 10) 0 2) DegreeTwoThreeSpectrum3290.graph sourceMap1627=true := by decide +kernel
theorem fusedMap1627_checked : acceptsGraphIso
    (fused (graph core1627) (root 10) 0 2) DegreeTwoThreeSpectrum2636.graph fusedMap1627=true := by decide +kernel
theorem certified1627 : Certified (graph core1627) (root 10) 0 2 :=
  of_native_maps core1627 DegreeTwoThreeSpectrum3290.graph DegreeTwoThreeSpectrum2636.graph
    sourceMap1627 fusedMap1627 sourceMap1627_checked fusedMap1627_checked
    DegreeTwoThreeFiniteComparisons.comparison1627
#print axioms sourceMap1627_checked
#print axioms fusedMap1627_checked
#print axioms certified1627
def sourceMap1627swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1627swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1627swap_checked : acceptsGraphIso
    (source (graph core1627) (root 10) 2 0) DegreeTwoThreeSpectrum3290.graph sourceMap1627swap=true := by decide +kernel
theorem fusedMap1627swap_checked : acceptsGraphIso
    (fused (graph core1627) (root 10) 2 0) DegreeTwoThreeSpectrum2636.graph fusedMap1627swap=true := by decide +kernel
theorem certified1627swap : Certified (graph core1627) (root 10) 2 0 :=
  of_native_maps core1627 DegreeTwoThreeSpectrum3290.graph DegreeTwoThreeSpectrum2636.graph
    sourceMap1627swap fusedMap1627swap sourceMap1627swap_checked fusedMap1627swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1627
#print axioms sourceMap1627swap_checked
#print axioms fusedMap1627swap_checked
#print axioms certified1627swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
