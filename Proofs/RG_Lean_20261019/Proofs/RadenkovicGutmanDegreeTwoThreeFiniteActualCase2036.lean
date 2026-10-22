/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2036 : Family 10 := level10.get ⟨1725,by decide⟩
def sourceMap2036 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2036 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2036_checked : acceptsGraphIso
    (source (graph core2036) (root 10) 0 2) DegreeTwoThreeSpectrum3831.graph sourceMap2036=true := by decide +kernel
theorem fusedMap2036_checked : acceptsGraphIso
    (fused (graph core2036) (root 10) 0 2) DegreeTwoThreeSpectrum3419.graph fusedMap2036=true := by decide +kernel
theorem certified2036 : Certified (graph core2036) (root 10) 0 2 :=
  of_native_maps core2036 DegreeTwoThreeSpectrum3831.graph DegreeTwoThreeSpectrum3419.graph
    sourceMap2036 fusedMap2036 sourceMap2036_checked fusedMap2036_checked
    DegreeTwoThreeFiniteComparisons.comparison2036
#print axioms sourceMap2036_checked
#print axioms fusedMap2036_checked
#print axioms certified2036
def sourceMap2036swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2036swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2036swap_checked : acceptsGraphIso
    (source (graph core2036) (root 10) 2 0) DegreeTwoThreeSpectrum3831.graph sourceMap2036swap=true := by decide +kernel
theorem fusedMap2036swap_checked : acceptsGraphIso
    (fused (graph core2036) (root 10) 2 0) DegreeTwoThreeSpectrum3419.graph fusedMap2036swap=true := by decide +kernel
theorem certified2036swap : Certified (graph core2036) (root 10) 2 0 :=
  of_native_maps core2036 DegreeTwoThreeSpectrum3831.graph DegreeTwoThreeSpectrum3419.graph
    sourceMap2036swap fusedMap2036swap sourceMap2036swap_checked fusedMap2036swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2036
#print axioms sourceMap2036swap_checked
#print axioms fusedMap2036swap_checked
#print axioms certified2036swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
