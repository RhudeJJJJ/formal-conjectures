/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1453 : Family 10 := level10.get ⟨117,by decide⟩
def sourceMap1453 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1453 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1453_checked : acceptsGraphIso
    (source (graph core1453) (root 10) 0 2) DegreeTwoThreeSpectrum2799.graph sourceMap1453=true := by decide +kernel
theorem fusedMap1453_checked : acceptsGraphIso
    (fused (graph core1453) (root 10) 0 2) DegreeTwoThreeSpectrum2376.graph fusedMap1453=true := by decide +kernel
theorem certified1453 : Certified (graph core1453) (root 10) 0 2 :=
  of_native_maps core1453 DegreeTwoThreeSpectrum2799.graph DegreeTwoThreeSpectrum2376.graph
    sourceMap1453 fusedMap1453 sourceMap1453_checked fusedMap1453_checked
    DegreeTwoThreeFiniteComparisons.comparison1453
#print axioms sourceMap1453_checked
#print axioms fusedMap1453_checked
#print axioms certified1453
def sourceMap1453swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1453swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1453swap_checked : acceptsGraphIso
    (source (graph core1453) (root 10) 2 0) DegreeTwoThreeSpectrum2799.graph sourceMap1453swap=true := by decide +kernel
theorem fusedMap1453swap_checked : acceptsGraphIso
    (fused (graph core1453) (root 10) 2 0) DegreeTwoThreeSpectrum2376.graph fusedMap1453swap=true := by decide +kernel
theorem certified1453swap : Certified (graph core1453) (root 10) 2 0 :=
  of_native_maps core1453 DegreeTwoThreeSpectrum2799.graph DegreeTwoThreeSpectrum2376.graph
    sourceMap1453swap fusedMap1453swap sourceMap1453swap_checked fusedMap1453swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1453
#print axioms sourceMap1453swap_checked
#print axioms fusedMap1453swap_checked
#print axioms certified1453swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
