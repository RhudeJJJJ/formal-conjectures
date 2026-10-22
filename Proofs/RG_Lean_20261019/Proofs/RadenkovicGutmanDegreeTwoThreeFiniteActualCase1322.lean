/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1322 : Family 9 := level9.get ⟨408,by decide⟩
def sourceMap1322 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,13,10,11,12] (sourceLabel 9 0 2 v)
def fusedMap1322 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 0 2 v)
theorem sourceMap1322_checked : acceptsGraphIso
    (source (graph core1322) (root 9) 0 2) DegreeTwoThreeSpectrum2066.graph sourceMap1322=true := by decide +kernel
theorem fusedMap1322_checked : acceptsGraphIso
    (fused (graph core1322) (root 9) 0 2) DegreeTwoThreeSpectrum2076.graph fusedMap1322=true := by decide +kernel
theorem certified1322 : Certified (graph core1322) (root 9) 0 2 :=
  of_native_maps core1322 DegreeTwoThreeSpectrum2066.graph DegreeTwoThreeSpectrum2076.graph
    sourceMap1322 fusedMap1322 sourceMap1322_checked fusedMap1322_checked
    DegreeTwoThreeFiniteComparisons.comparison1322
#print axioms sourceMap1322_checked
#print axioms fusedMap1322_checked
#print axioms certified1322
def sourceMap1322swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11,12,13] (sourceLabel 9 2 0 v)
def fusedMap1322swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,6,7,8,9] (fusedLabel 9 2 0 v)
theorem sourceMap1322swap_checked : acceptsGraphIso
    (source (graph core1322) (root 9) 2 0) DegreeTwoThreeSpectrum2066.graph sourceMap1322swap=true := by decide +kernel
theorem fusedMap1322swap_checked : acceptsGraphIso
    (fused (graph core1322) (root 9) 2 0) DegreeTwoThreeSpectrum2076.graph fusedMap1322swap=true := by decide +kernel
theorem certified1322swap : Certified (graph core1322) (root 9) 2 0 :=
  of_native_maps core1322 DegreeTwoThreeSpectrum2066.graph DegreeTwoThreeSpectrum2076.graph
    sourceMap1322swap fusedMap1322swap sourceMap1322swap_checked fusedMap1322swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1322
#print axioms sourceMap1322swap_checked
#print axioms fusedMap1322swap_checked
#print axioms certified1322swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
