/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1467 : Family 10 := level10.get ⟨174,by decide⟩
def sourceMap1467 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,8,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1467 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,7,6,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1467_checked : acceptsGraphIso
    (source (graph core1467) (root 10) 0 2) DegreeTwoThreeSpectrum2895.graph sourceMap1467=true := by decide +kernel
theorem fusedMap1467_checked : acceptsGraphIso
    (fused (graph core1467) (root 10) 0 2) DegreeTwoThreeSpectrum2421.graph fusedMap1467=true := by decide +kernel
theorem certified1467 : Certified (graph core1467) (root 10) 0 2 :=
  of_native_maps core1467 DegreeTwoThreeSpectrum2895.graph DegreeTwoThreeSpectrum2421.graph
    sourceMap1467 fusedMap1467 sourceMap1467_checked fusedMap1467_checked
    DegreeTwoThreeFiniteComparisons.comparison1467
#print axioms sourceMap1467_checked
#print axioms fusedMap1467_checked
#print axioms certified1467
def sourceMap1467swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,8,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1467swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,7,6,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1467swap_checked : acceptsGraphIso
    (source (graph core1467) (root 10) 2 0) DegreeTwoThreeSpectrum2895.graph sourceMap1467swap=true := by decide +kernel
theorem fusedMap1467swap_checked : acceptsGraphIso
    (fused (graph core1467) (root 10) 2 0) DegreeTwoThreeSpectrum2421.graph fusedMap1467swap=true := by decide +kernel
theorem certified1467swap : Certified (graph core1467) (root 10) 2 0 :=
  of_native_maps core1467 DegreeTwoThreeSpectrum2895.graph DegreeTwoThreeSpectrum2421.graph
    sourceMap1467swap fusedMap1467swap sourceMap1467swap_checked fusedMap1467swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1467
#print axioms sourceMap1467swap_checked
#print axioms fusedMap1467swap_checked
#print axioms certified1467swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
