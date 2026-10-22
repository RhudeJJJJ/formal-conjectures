/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1606 : Family 10 := level10.get ⟨623,by decide⟩
def sourceMap1606 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1606 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1606_checked : acceptsGraphIso
    (source (graph core1606) (root 10) 0 2) DegreeTwoThreeSpectrum3310.graph sourceMap1606=true := by decide +kernel
theorem fusedMap1606_checked : acceptsGraphIso
    (fused (graph core1606) (root 10) 0 2) DegreeTwoThreeSpectrum2568.graph fusedMap1606=true := by decide +kernel
theorem certified1606 : Certified (graph core1606) (root 10) 0 2 :=
  of_native_maps core1606 DegreeTwoThreeSpectrum3310.graph DegreeTwoThreeSpectrum2568.graph
    sourceMap1606 fusedMap1606 sourceMap1606_checked fusedMap1606_checked
    DegreeTwoThreeFiniteComparisons.comparison1606
#print axioms sourceMap1606_checked
#print axioms fusedMap1606_checked
#print axioms certified1606
def sourceMap1606swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1606swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1606swap_checked : acceptsGraphIso
    (source (graph core1606) (root 10) 2 0) DegreeTwoThreeSpectrum3310.graph sourceMap1606swap=true := by decide +kernel
theorem fusedMap1606swap_checked : acceptsGraphIso
    (fused (graph core1606) (root 10) 2 0) DegreeTwoThreeSpectrum2568.graph fusedMap1606swap=true := by decide +kernel
theorem certified1606swap : Certified (graph core1606) (root 10) 2 0 :=
  of_native_maps core1606 DegreeTwoThreeSpectrum3310.graph DegreeTwoThreeSpectrum2568.graph
    sourceMap1606swap fusedMap1606swap sourceMap1606swap_checked fusedMap1606swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1606
#print axioms sourceMap1606swap_checked
#print axioms fusedMap1606swap_checked
#print axioms certified1606swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
