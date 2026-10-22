/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1692 : Family 10 := level10.get ⟨861,by decide⟩
def sourceMap1692 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1692 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1692_checked : acceptsGraphIso
    (source (graph core1692) (root 10) 0 2) DegreeTwoThreeSpectrum3676.graph sourceMap1692=true := by decide +kernel
theorem fusedMap1692_checked : acceptsGraphIso
    (fused (graph core1692) (root 10) 0 2) DegreeTwoThreeSpectrum2853.graph fusedMap1692=true := by decide +kernel
theorem certified1692 : Certified (graph core1692) (root 10) 0 2 :=
  of_native_maps core1692 DegreeTwoThreeSpectrum3676.graph DegreeTwoThreeSpectrum2853.graph
    sourceMap1692 fusedMap1692 sourceMap1692_checked fusedMap1692_checked
    DegreeTwoThreeFiniteComparisons.comparison1692
#print axioms sourceMap1692_checked
#print axioms fusedMap1692_checked
#print axioms certified1692
def sourceMap1692swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1692swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1692swap_checked : acceptsGraphIso
    (source (graph core1692) (root 10) 2 0) DegreeTwoThreeSpectrum3676.graph sourceMap1692swap=true := by decide +kernel
theorem fusedMap1692swap_checked : acceptsGraphIso
    (fused (graph core1692) (root 10) 2 0) DegreeTwoThreeSpectrum2853.graph fusedMap1692swap=true := by decide +kernel
theorem certified1692swap : Certified (graph core1692) (root 10) 2 0 :=
  of_native_maps core1692 DegreeTwoThreeSpectrum3676.graph DegreeTwoThreeSpectrum2853.graph
    sourceMap1692swap fusedMap1692swap sourceMap1692swap_checked fusedMap1692swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1692
#print axioms sourceMap1692swap_checked
#print axioms fusedMap1692swap_checked
#print axioms certified1692swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
