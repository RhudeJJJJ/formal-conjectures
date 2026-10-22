/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2713 : Family 10 := level10.get ⟨857,by decide⟩
def sourceMap2713 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2713 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2713_checked : acceptsGraphIso
    (source (graph core2713) (root 10) 0 4) DegreeTwoThreeSpectrum6907.graph sourceMap2713=true := by decide +kernel
theorem fusedMap2713_checked : acceptsGraphIso
    (fused (graph core2713) (root 10) 0 4) DegreeTwoThreeSpectrum5693.graph fusedMap2713=true := by decide +kernel
theorem certified2713 : Certified (graph core2713) (root 10) 0 4 :=
  of_native_maps core2713 DegreeTwoThreeSpectrum6907.graph DegreeTwoThreeSpectrum5693.graph
    sourceMap2713 fusedMap2713 sourceMap2713_checked fusedMap2713_checked
    DegreeTwoThreeFiniteComparisons.comparison2713
#print axioms sourceMap2713_checked
#print axioms fusedMap2713_checked
#print axioms certified2713
def sourceMap2713swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2713swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2713swap_checked : acceptsGraphIso
    (source (graph core2713) (root 10) 4 0) DegreeTwoThreeSpectrum6907.graph sourceMap2713swap=true := by decide +kernel
theorem fusedMap2713swap_checked : acceptsGraphIso
    (fused (graph core2713) (root 10) 4 0) DegreeTwoThreeSpectrum5693.graph fusedMap2713swap=true := by decide +kernel
theorem certified2713swap : Certified (graph core2713) (root 10) 4 0 :=
  of_native_maps core2713 DegreeTwoThreeSpectrum6907.graph DegreeTwoThreeSpectrum5693.graph
    sourceMap2713swap fusedMap2713swap sourceMap2713swap_checked fusedMap2713swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2713
#print axioms sourceMap2713swap_checked
#print axioms fusedMap2713swap_checked
#print axioms certified2713swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
