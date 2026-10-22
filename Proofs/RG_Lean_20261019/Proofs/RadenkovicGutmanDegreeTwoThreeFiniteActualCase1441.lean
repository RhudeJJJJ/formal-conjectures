/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1441 : Family 10 := level10.get ⟨66,by decide⟩
def sourceMap1441 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1441 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1441_checked : acceptsGraphIso
    (source (graph core1441) (root 10) 0 2) DegreeTwoThreeSpectrum2555.graph sourceMap1441=true := by decide +kernel
theorem fusedMap1441_checked : acceptsGraphIso
    (fused (graph core1441) (root 10) 0 2) DegreeTwoThreeSpectrum2326.graph fusedMap1441=true := by decide +kernel
theorem certified1441 : Certified (graph core1441) (root 10) 0 2 :=
  of_native_maps core1441 DegreeTwoThreeSpectrum2555.graph DegreeTwoThreeSpectrum2326.graph
    sourceMap1441 fusedMap1441 sourceMap1441_checked fusedMap1441_checked
    DegreeTwoThreeFiniteComparisons.comparison1441
#print axioms sourceMap1441_checked
#print axioms fusedMap1441_checked
#print axioms certified1441
def sourceMap1441swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1441swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1441swap_checked : acceptsGraphIso
    (source (graph core1441) (root 10) 2 0) DegreeTwoThreeSpectrum2555.graph sourceMap1441swap=true := by decide +kernel
theorem fusedMap1441swap_checked : acceptsGraphIso
    (fused (graph core1441) (root 10) 2 0) DegreeTwoThreeSpectrum2326.graph fusedMap1441swap=true := by decide +kernel
theorem certified1441swap : Certified (graph core1441) (root 10) 2 0 :=
  of_native_maps core1441 DegreeTwoThreeSpectrum2555.graph DegreeTwoThreeSpectrum2326.graph
    sourceMap1441swap fusedMap1441swap sourceMap1441swap_checked fusedMap1441swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1441
#print axioms sourceMap1441swap_checked
#print axioms fusedMap1441swap_checked
#print axioms certified1441swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
