/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1469 : Family 10 := level10.get ⟨180,by decide⟩
def sourceMap1469 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,10,11,12,13,14,8,9,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1469 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,8,6,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1469_checked : acceptsGraphIso
    (source (graph core1469) (root 10) 0 2) DegreeTwoThreeSpectrum2884.graph sourceMap1469=true := by decide +kernel
theorem fusedMap1469_checked : acceptsGraphIso
    (fused (graph core1469) (root 10) 0 2) DegreeTwoThreeSpectrum2418.graph fusedMap1469=true := by decide +kernel
theorem certified1469 : Certified (graph core1469) (root 10) 0 2 :=
  of_native_maps core1469 DegreeTwoThreeSpectrum2884.graph DegreeTwoThreeSpectrum2418.graph
    sourceMap1469 fusedMap1469 sourceMap1469_checked fusedMap1469_checked
    DegreeTwoThreeFiniteComparisons.comparison1469
#print axioms sourceMap1469_checked
#print axioms fusedMap1469_checked
#print axioms certified1469
def sourceMap1469swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,10,11,12,13,14,8,9,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1469swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,8,6,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1469swap_checked : acceptsGraphIso
    (source (graph core1469) (root 10) 2 0) DegreeTwoThreeSpectrum2884.graph sourceMap1469swap=true := by decide +kernel
theorem fusedMap1469swap_checked : acceptsGraphIso
    (fused (graph core1469) (root 10) 2 0) DegreeTwoThreeSpectrum2418.graph fusedMap1469swap=true := by decide +kernel
theorem certified1469swap : Certified (graph core1469) (root 10) 2 0 :=
  of_native_maps core1469 DegreeTwoThreeSpectrum2884.graph DegreeTwoThreeSpectrum2418.graph
    sourceMap1469swap fusedMap1469swap sourceMap1469swap_checked fusedMap1469swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1469
#print axioms sourceMap1469swap_checked
#print axioms fusedMap1469swap_checked
#print axioms certified1469swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
