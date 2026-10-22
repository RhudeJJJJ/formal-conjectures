/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1678 : Family 10 := level10.get ⟨821,by decide⟩
def sourceMap1678 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1678 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1678_checked : acceptsGraphIso
    (source (graph core1678) (root 10) 0 2) DegreeTwoThreeSpectrum2807.graph sourceMap1678=true := by decide +kernel
theorem fusedMap1678_checked : acceptsGraphIso
    (fused (graph core1678) (root 10) 0 2) DegreeTwoThreeSpectrum2804.graph fusedMap1678=true := by decide +kernel
theorem certified1678 : Certified (graph core1678) (root 10) 0 2 :=
  of_native_maps core1678 DegreeTwoThreeSpectrum2807.graph DegreeTwoThreeSpectrum2804.graph
    sourceMap1678 fusedMap1678 sourceMap1678_checked fusedMap1678_checked
    DegreeTwoThreeFiniteComparisons.comparison1678
#print axioms sourceMap1678_checked
#print axioms fusedMap1678_checked
#print axioms certified1678
def sourceMap1678swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1678swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1678swap_checked : acceptsGraphIso
    (source (graph core1678) (root 10) 2 0) DegreeTwoThreeSpectrum2807.graph sourceMap1678swap=true := by decide +kernel
theorem fusedMap1678swap_checked : acceptsGraphIso
    (fused (graph core1678) (root 10) 2 0) DegreeTwoThreeSpectrum2804.graph fusedMap1678swap=true := by decide +kernel
theorem certified1678swap : Certified (graph core1678) (root 10) 2 0 :=
  of_native_maps core1678 DegreeTwoThreeSpectrum2807.graph DegreeTwoThreeSpectrum2804.graph
    sourceMap1678swap fusedMap1678swap sourceMap1678swap_checked fusedMap1678swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1678
#print axioms sourceMap1678swap_checked
#print axioms fusedMap1678swap_checked
#print axioms certified1678swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
