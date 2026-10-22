/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1628 : Family 10 := level10.get ⟨676,by decide⟩
def sourceMap1628 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1628 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1628_checked : acceptsGraphIso
    (source (graph core1628) (root 10) 0 2) DegreeTwoThreeSpectrum3353.graph sourceMap1628=true := by decide +kernel
theorem fusedMap1628_checked : acceptsGraphIso
    (fused (graph core1628) (root 10) 0 2) DegreeTwoThreeSpectrum2637.graph fusedMap1628=true := by decide +kernel
theorem certified1628 : Certified (graph core1628) (root 10) 0 2 :=
  of_native_maps core1628 DegreeTwoThreeSpectrum3353.graph DegreeTwoThreeSpectrum2637.graph
    sourceMap1628 fusedMap1628 sourceMap1628_checked fusedMap1628_checked
    DegreeTwoThreeFiniteComparisons.comparison1628
#print axioms sourceMap1628_checked
#print axioms fusedMap1628_checked
#print axioms certified1628
def sourceMap1628swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1628swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1628swap_checked : acceptsGraphIso
    (source (graph core1628) (root 10) 2 0) DegreeTwoThreeSpectrum3353.graph sourceMap1628swap=true := by decide +kernel
theorem fusedMap1628swap_checked : acceptsGraphIso
    (fused (graph core1628) (root 10) 2 0) DegreeTwoThreeSpectrum2637.graph fusedMap1628swap=true := by decide +kernel
theorem certified1628swap : Certified (graph core1628) (root 10) 2 0 :=
  of_native_maps core1628 DegreeTwoThreeSpectrum3353.graph DegreeTwoThreeSpectrum2637.graph
    sourceMap1628swap fusedMap1628swap sourceMap1628swap_checked fusedMap1628swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1628
#print axioms sourceMap1628swap_checked
#print axioms fusedMap1628swap_checked
#print axioms certified1628swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
