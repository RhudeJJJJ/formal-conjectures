/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1459 : Family 10 := level10.get ⟨143,by decide⟩
def sourceMap1459 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,6,7,8,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1459 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1459_checked : acceptsGraphIso
    (source (graph core1459) (root 10) 0 2) DegreeTwoThreeSpectrum2852.graph sourceMap1459=true := by decide +kernel
theorem fusedMap1459_checked : acceptsGraphIso
    (fused (graph core1459) (root 10) 0 2) DegreeTwoThreeSpectrum2403.graph fusedMap1459=true := by decide +kernel
theorem certified1459 : Certified (graph core1459) (root 10) 0 2 :=
  of_native_maps core1459 DegreeTwoThreeSpectrum2852.graph DegreeTwoThreeSpectrum2403.graph
    sourceMap1459 fusedMap1459 sourceMap1459_checked fusedMap1459_checked
    DegreeTwoThreeFiniteComparisons.comparison1459
#print axioms sourceMap1459_checked
#print axioms fusedMap1459_checked
#print axioms certified1459
def sourceMap1459swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,6,7,3,4,5,8] (sourceLabel 10 2 0 v)
def fusedMap1459swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1459swap_checked : acceptsGraphIso
    (source (graph core1459) (root 10) 2 0) DegreeTwoThreeSpectrum2852.graph sourceMap1459swap=true := by decide +kernel
theorem fusedMap1459swap_checked : acceptsGraphIso
    (fused (graph core1459) (root 10) 2 0) DegreeTwoThreeSpectrum2403.graph fusedMap1459swap=true := by decide +kernel
theorem certified1459swap : Certified (graph core1459) (root 10) 2 0 :=
  of_native_maps core1459 DegreeTwoThreeSpectrum2852.graph DegreeTwoThreeSpectrum2403.graph
    sourceMap1459swap fusedMap1459swap sourceMap1459swap_checked fusedMap1459swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1459
#print axioms sourceMap1459swap_checked
#print axioms fusedMap1459swap_checked
#print axioms certified1459swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
