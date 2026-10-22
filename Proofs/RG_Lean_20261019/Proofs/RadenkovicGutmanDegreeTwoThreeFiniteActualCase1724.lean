/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1724 : Family 10 := level10.get ⟨945,by decide⟩
def sourceMap1724 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1724 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1724_checked : acceptsGraphIso
    (source (graph core1724) (root 10) 0 2) DegreeTwoThreeSpectrum3712.graph sourceMap1724=true := by decide +kernel
theorem fusedMap1724_checked : acceptsGraphIso
    (fused (graph core1724) (root 10) 0 2) DegreeTwoThreeSpectrum2966.graph fusedMap1724=true := by decide +kernel
theorem certified1724 : Certified (graph core1724) (root 10) 0 2 :=
  of_native_maps core1724 DegreeTwoThreeSpectrum3712.graph DegreeTwoThreeSpectrum2966.graph
    sourceMap1724 fusedMap1724 sourceMap1724_checked fusedMap1724_checked
    DegreeTwoThreeFiniteComparisons.comparison1724
#print axioms sourceMap1724_checked
#print axioms fusedMap1724_checked
#print axioms certified1724
def sourceMap1724swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1724swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1724swap_checked : acceptsGraphIso
    (source (graph core1724) (root 10) 2 0) DegreeTwoThreeSpectrum3712.graph sourceMap1724swap=true := by decide +kernel
theorem fusedMap1724swap_checked : acceptsGraphIso
    (fused (graph core1724) (root 10) 2 0) DegreeTwoThreeSpectrum2966.graph fusedMap1724swap=true := by decide +kernel
theorem certified1724swap : Certified (graph core1724) (root 10) 2 0 :=
  of_native_maps core1724 DegreeTwoThreeSpectrum3712.graph DegreeTwoThreeSpectrum2966.graph
    sourceMap1724swap fusedMap1724swap sourceMap1724swap_checked fusedMap1724swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1724
#print axioms sourceMap1724swap_checked
#print axioms fusedMap1724swap_checked
#print axioms certified1724swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
