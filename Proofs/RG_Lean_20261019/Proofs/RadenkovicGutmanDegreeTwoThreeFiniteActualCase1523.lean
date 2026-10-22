/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1523 : Family 10 := level10.get ⟨364,by decide⟩
def sourceMap1523 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1523 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1523_checked : acceptsGraphIso
    (source (graph core1523) (root 10) 0 2) DegreeTwoThreeSpectrum2797.graph sourceMap1523=true := by decide +kernel
theorem fusedMap1523_checked : acceptsGraphIso
    (fused (graph core1523) (root 10) 0 2) DegreeTwoThreeSpectrum2810.graph fusedMap1523=true := by decide +kernel
theorem certified1523 : Certified (graph core1523) (root 10) 0 2 :=
  of_native_maps core1523 DegreeTwoThreeSpectrum2797.graph DegreeTwoThreeSpectrum2810.graph
    sourceMap1523 fusedMap1523 sourceMap1523_checked fusedMap1523_checked
    DegreeTwoThreeFiniteComparisons.comparison1523
#print axioms sourceMap1523_checked
#print axioms fusedMap1523_checked
#print axioms certified1523
def sourceMap1523swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1523swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1523swap_checked : acceptsGraphIso
    (source (graph core1523) (root 10) 2 0) DegreeTwoThreeSpectrum2797.graph sourceMap1523swap=true := by decide +kernel
theorem fusedMap1523swap_checked : acceptsGraphIso
    (fused (graph core1523) (root 10) 2 0) DegreeTwoThreeSpectrum2810.graph fusedMap1523swap=true := by decide +kernel
theorem certified1523swap : Certified (graph core1523) (root 10) 2 0 :=
  of_native_maps core1523 DegreeTwoThreeSpectrum2797.graph DegreeTwoThreeSpectrum2810.graph
    sourceMap1523swap fusedMap1523swap sourceMap1523swap_checked fusedMap1523swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1523
#print axioms sourceMap1523swap_checked
#print axioms fusedMap1523swap_checked
#print axioms certified1523swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
