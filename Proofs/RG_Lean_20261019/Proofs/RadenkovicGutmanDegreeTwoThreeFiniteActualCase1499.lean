/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1499 : Family 10 := level10.get ⟨281,by decide⟩
def sourceMap1499 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1499 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1499_checked : acceptsGraphIso
    (source (graph core1499) (root 10) 0 2) DegreeTwoThreeSpectrum2628.graph sourceMap1499=true := by decide +kernel
theorem fusedMap1499_checked : acceptsGraphIso
    (fused (graph core1499) (root 10) 0 2) DegreeTwoThreeSpectrum2641.graph fusedMap1499=true := by decide +kernel
theorem certified1499 : Certified (graph core1499) (root 10) 0 2 :=
  of_native_maps core1499 DegreeTwoThreeSpectrum2628.graph DegreeTwoThreeSpectrum2641.graph
    sourceMap1499 fusedMap1499 sourceMap1499_checked fusedMap1499_checked
    DegreeTwoThreeFiniteComparisons.comparison1499
#print axioms sourceMap1499_checked
#print axioms fusedMap1499_checked
#print axioms certified1499
def sourceMap1499swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1499swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1499swap_checked : acceptsGraphIso
    (source (graph core1499) (root 10) 2 0) DegreeTwoThreeSpectrum2628.graph sourceMap1499swap=true := by decide +kernel
theorem fusedMap1499swap_checked : acceptsGraphIso
    (fused (graph core1499) (root 10) 2 0) DegreeTwoThreeSpectrum2641.graph fusedMap1499swap=true := by decide +kernel
theorem certified1499swap : Certified (graph core1499) (root 10) 2 0 :=
  of_native_maps core1499 DegreeTwoThreeSpectrum2628.graph DegreeTwoThreeSpectrum2641.graph
    sourceMap1499swap fusedMap1499swap sourceMap1499swap_checked fusedMap1499swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1499
#print axioms sourceMap1499swap_checked
#print axioms fusedMap1499swap_checked
#print axioms certified1499swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
