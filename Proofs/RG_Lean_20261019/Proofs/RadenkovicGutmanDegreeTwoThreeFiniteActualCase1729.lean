/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1729 : Family 10 := level10.get ⟨954,by decide⟩
def sourceMap1729 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1729 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,5,6,7,1,2,3,4] (fusedLabel 10 0 2 v)
theorem sourceMap1729_checked : acceptsGraphIso
    (source (graph core1729) (root 10) 0 2) DegreeTwoThreeSpectrum3628.graph sourceMap1729=true := by decide +kernel
theorem fusedMap1729_checked : acceptsGraphIso
    (fused (graph core1729) (root 10) 0 2) DegreeTwoThreeSpectrum2957.graph fusedMap1729=true := by decide +kernel
theorem certified1729 : Certified (graph core1729) (root 10) 0 2 :=
  of_native_maps core1729 DegreeTwoThreeSpectrum3628.graph DegreeTwoThreeSpectrum2957.graph
    sourceMap1729 fusedMap1729 sourceMap1729_checked fusedMap1729_checked
    DegreeTwoThreeFiniteComparisons.comparison1729
#print axioms sourceMap1729_checked
#print axioms fusedMap1729_checked
#print axioms certified1729
def sourceMap1729swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1729swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,5,6,7,1,2,3,4] (fusedLabel 10 2 0 v)
theorem sourceMap1729swap_checked : acceptsGraphIso
    (source (graph core1729) (root 10) 2 0) DegreeTwoThreeSpectrum3628.graph sourceMap1729swap=true := by decide +kernel
theorem fusedMap1729swap_checked : acceptsGraphIso
    (fused (graph core1729) (root 10) 2 0) DegreeTwoThreeSpectrum2957.graph fusedMap1729swap=true := by decide +kernel
theorem certified1729swap : Certified (graph core1729) (root 10) 2 0 :=
  of_native_maps core1729 DegreeTwoThreeSpectrum3628.graph DegreeTwoThreeSpectrum2957.graph
    sourceMap1729swap fusedMap1729swap sourceMap1729swap_checked fusedMap1729swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1729
#print axioms sourceMap1729swap_checked
#print axioms fusedMap1729swap_checked
#print axioms certified1729swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
