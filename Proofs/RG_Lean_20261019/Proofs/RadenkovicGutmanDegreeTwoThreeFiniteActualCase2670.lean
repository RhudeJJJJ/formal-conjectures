/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2670 : Family 10 := level10.get ⟨736,by decide⟩
def sourceMap2670 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2670 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2670_checked : acceptsGraphIso
    (source (graph core2670) (root 10) 0 4) DegreeTwoThreeSpectrum6619.graph sourceMap2670=true := by decide +kernel
theorem fusedMap2670_checked : acceptsGraphIso
    (fused (graph core2670) (root 10) 0 4) DegreeTwoThreeSpectrum5494.graph fusedMap2670=true := by decide +kernel
theorem certified2670 : Certified (graph core2670) (root 10) 0 4 :=
  of_native_maps core2670 DegreeTwoThreeSpectrum6619.graph DegreeTwoThreeSpectrum5494.graph
    sourceMap2670 fusedMap2670 sourceMap2670_checked fusedMap2670_checked
    DegreeTwoThreeFiniteComparisons.comparison2670
#print axioms sourceMap2670_checked
#print axioms fusedMap2670_checked
#print axioms certified2670
def sourceMap2670swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2670swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2670swap_checked : acceptsGraphIso
    (source (graph core2670) (root 10) 4 0) DegreeTwoThreeSpectrum6619.graph sourceMap2670swap=true := by decide +kernel
theorem fusedMap2670swap_checked : acceptsGraphIso
    (fused (graph core2670) (root 10) 4 0) DegreeTwoThreeSpectrum5494.graph fusedMap2670swap=true := by decide +kernel
theorem certified2670swap : Certified (graph core2670) (root 10) 4 0 :=
  of_native_maps core2670 DegreeTwoThreeSpectrum6619.graph DegreeTwoThreeSpectrum5494.graph
    sourceMap2670swap fusedMap2670swap sourceMap2670swap_checked fusedMap2670swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2670
#print axioms sourceMap2670swap_checked
#print axioms fusedMap2670swap_checked
#print axioms certified2670swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
