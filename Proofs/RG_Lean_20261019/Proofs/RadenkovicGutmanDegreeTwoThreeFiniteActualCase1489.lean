/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1489 : Family 10 := level10.get ⟨256,by decide⟩
def sourceMap1489 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1489 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1489_checked : acceptsGraphIso
    (source (graph core1489) (root 10) 0 2) DegreeTwoThreeSpectrum2595.graph sourceMap1489=true := by decide +kernel
theorem fusedMap1489_checked : acceptsGraphIso
    (fused (graph core1489) (root 10) 0 2) DegreeTwoThreeSpectrum2600.graph fusedMap1489=true := by decide +kernel
theorem certified1489 : Certified (graph core1489) (root 10) 0 2 :=
  of_native_maps core1489 DegreeTwoThreeSpectrum2595.graph DegreeTwoThreeSpectrum2600.graph
    sourceMap1489 fusedMap1489 sourceMap1489_checked fusedMap1489_checked
    DegreeTwoThreeFiniteComparisons.comparison1489
#print axioms sourceMap1489_checked
#print axioms fusedMap1489_checked
#print axioms certified1489
def sourceMap1489swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1489swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1489swap_checked : acceptsGraphIso
    (source (graph core1489) (root 10) 2 0) DegreeTwoThreeSpectrum2595.graph sourceMap1489swap=true := by decide +kernel
theorem fusedMap1489swap_checked : acceptsGraphIso
    (fused (graph core1489) (root 10) 2 0) DegreeTwoThreeSpectrum2600.graph fusedMap1489swap=true := by decide +kernel
theorem certified1489swap : Certified (graph core1489) (root 10) 2 0 :=
  of_native_maps core1489 DegreeTwoThreeSpectrum2595.graph DegreeTwoThreeSpectrum2600.graph
    sourceMap1489swap fusedMap1489swap sourceMap1489swap_checked fusedMap1489swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1489
#print axioms sourceMap1489swap_checked
#print axioms fusedMap1489swap_checked
#print axioms certified1489swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
