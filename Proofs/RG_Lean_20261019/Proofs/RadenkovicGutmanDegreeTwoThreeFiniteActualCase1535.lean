/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1535 : Family 10 := level10.get ⟨410,by decide⟩
def sourceMap1535 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1535 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1535_checked : acceptsGraphIso
    (source (graph core1535) (root 10) 0 2) DegreeTwoThreeSpectrum2898.graph sourceMap1535=true := by decide +kernel
theorem fusedMap1535_checked : acceptsGraphIso
    (fused (graph core1535) (root 10) 0 2) DegreeTwoThreeSpectrum2924.graph fusedMap1535=true := by decide +kernel
theorem certified1535 : Certified (graph core1535) (root 10) 0 2 :=
  of_native_maps core1535 DegreeTwoThreeSpectrum2898.graph DegreeTwoThreeSpectrum2924.graph
    sourceMap1535 fusedMap1535 sourceMap1535_checked fusedMap1535_checked
    DegreeTwoThreeFiniteComparisons.comparison1535
#print axioms sourceMap1535_checked
#print axioms fusedMap1535_checked
#print axioms certified1535
def sourceMap1535swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1535swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1535swap_checked : acceptsGraphIso
    (source (graph core1535) (root 10) 2 0) DegreeTwoThreeSpectrum2898.graph sourceMap1535swap=true := by decide +kernel
theorem fusedMap1535swap_checked : acceptsGraphIso
    (fused (graph core1535) (root 10) 2 0) DegreeTwoThreeSpectrum2924.graph fusedMap1535swap=true := by decide +kernel
theorem certified1535swap : Certified (graph core1535) (root 10) 2 0 :=
  of_native_maps core1535 DegreeTwoThreeSpectrum2898.graph DegreeTwoThreeSpectrum2924.graph
    sourceMap1535swap fusedMap1535swap sourceMap1535swap_checked fusedMap1535swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1535
#print axioms sourceMap1535swap_checked
#print axioms fusedMap1535swap_checked
#print axioms certified1535swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
