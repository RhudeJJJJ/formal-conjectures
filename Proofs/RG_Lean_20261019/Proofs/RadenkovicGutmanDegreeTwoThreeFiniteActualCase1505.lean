/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1505 : Family 10 := level10.get ⟨308,by decide⟩
def sourceMap1505 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1505 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1505_checked : acceptsGraphIso
    (source (graph core1505) (root 10) 0 2) DegreeTwoThreeSpectrum2699.graph sourceMap1505=true := by decide +kernel
theorem fusedMap1505_checked : acceptsGraphIso
    (fused (graph core1505) (root 10) 0 2) DegreeTwoThreeSpectrum2701.graph fusedMap1505=true := by decide +kernel
theorem certified1505 : Certified (graph core1505) (root 10) 0 2 :=
  of_native_maps core1505 DegreeTwoThreeSpectrum2699.graph DegreeTwoThreeSpectrum2701.graph
    sourceMap1505 fusedMap1505 sourceMap1505_checked fusedMap1505_checked
    DegreeTwoThreeFiniteComparisons.comparison1505
#print axioms sourceMap1505_checked
#print axioms fusedMap1505_checked
#print axioms certified1505
def sourceMap1505swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1505swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1505swap_checked : acceptsGraphIso
    (source (graph core1505) (root 10) 2 0) DegreeTwoThreeSpectrum2699.graph sourceMap1505swap=true := by decide +kernel
theorem fusedMap1505swap_checked : acceptsGraphIso
    (fused (graph core1505) (root 10) 2 0) DegreeTwoThreeSpectrum2701.graph fusedMap1505swap=true := by decide +kernel
theorem certified1505swap : Certified (graph core1505) (root 10) 2 0 :=
  of_native_maps core1505 DegreeTwoThreeSpectrum2699.graph DegreeTwoThreeSpectrum2701.graph
    sourceMap1505swap fusedMap1505swap sourceMap1505swap_checked fusedMap1505swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1505
#print axioms sourceMap1505swap_checked
#print axioms fusedMap1505swap_checked
#print axioms certified1505swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
