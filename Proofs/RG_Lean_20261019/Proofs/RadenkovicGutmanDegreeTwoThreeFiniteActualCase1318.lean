/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1318 : Family 9 := level9.get ⟨402,by decide⟩
def sourceMap1318 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1318 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 0 2 v)
theorem sourceMap1318_checked : acceptsGraphIso
    (source (graph core1318) (root 9) 0 2) DegreeTwoThreeSpectrum2060.graph sourceMap1318=true := by decide +kernel
theorem fusedMap1318_checked : acceptsGraphIso
    (fused (graph core1318) (root 9) 0 2) DegreeTwoThreeSpectrum2064.graph fusedMap1318=true := by decide +kernel
theorem certified1318 : Certified (graph core1318) (root 9) 0 2 :=
  of_native_maps core1318 DegreeTwoThreeSpectrum2060.graph DegreeTwoThreeSpectrum2064.graph
    sourceMap1318 fusedMap1318 sourceMap1318_checked fusedMap1318_checked
    DegreeTwoThreeFiniteComparisons.comparison1318
#print axioms sourceMap1318_checked
#print axioms fusedMap1318_checked
#print axioms certified1318
def sourceMap1318swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1318swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,7,8,9,10] (fusedLabel 9 2 0 v)
theorem sourceMap1318swap_checked : acceptsGraphIso
    (source (graph core1318) (root 9) 2 0) DegreeTwoThreeSpectrum2060.graph sourceMap1318swap=true := by decide +kernel
theorem fusedMap1318swap_checked : acceptsGraphIso
    (fused (graph core1318) (root 9) 2 0) DegreeTwoThreeSpectrum2064.graph fusedMap1318swap=true := by decide +kernel
theorem certified1318swap : Certified (graph core1318) (root 9) 2 0 :=
  of_native_maps core1318 DegreeTwoThreeSpectrum2060.graph DegreeTwoThreeSpectrum2064.graph
    sourceMap1318swap fusedMap1318swap sourceMap1318swap_checked fusedMap1318swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1318
#print axioms sourceMap1318swap_checked
#print axioms fusedMap1318swap_checked
#print axioms certified1318swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
