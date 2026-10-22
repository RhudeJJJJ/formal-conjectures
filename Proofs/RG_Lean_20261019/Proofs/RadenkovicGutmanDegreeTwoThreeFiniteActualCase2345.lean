/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2345 : Family 9 := level9.get ⟨408,by decide⟩
def sourceMap2345 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2345 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2345_checked : acceptsGraphIso
    (source (graph core2345) (root 9) 0 4) DegreeTwoThreeSpectrum4372.graph sourceMap2345=true := by decide +kernel
theorem fusedMap2345_checked : acceptsGraphIso
    (fused (graph core2345) (root 9) 0 4) DegreeTwoThreeSpectrum4373.graph fusedMap2345=true := by decide +kernel
theorem certified2345 : Certified (graph core2345) (root 9) 0 4 :=
  of_native_maps core2345 DegreeTwoThreeSpectrum4372.graph DegreeTwoThreeSpectrum4373.graph
    sourceMap2345 fusedMap2345 sourceMap2345_checked fusedMap2345_checked
    DegreeTwoThreeFiniteComparisons.comparison2345
#print axioms sourceMap2345_checked
#print axioms fusedMap2345_checked
#print axioms certified2345
def sourceMap2345swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2345swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2345swap_checked : acceptsGraphIso
    (source (graph core2345) (root 9) 4 0) DegreeTwoThreeSpectrum4372.graph sourceMap2345swap=true := by decide +kernel
theorem fusedMap2345swap_checked : acceptsGraphIso
    (fused (graph core2345) (root 9) 4 0) DegreeTwoThreeSpectrum4373.graph fusedMap2345swap=true := by decide +kernel
theorem certified2345swap : Certified (graph core2345) (root 9) 4 0 :=
  of_native_maps core2345 DegreeTwoThreeSpectrum4372.graph DegreeTwoThreeSpectrum4373.graph
    sourceMap2345swap fusedMap2345swap sourceMap2345swap_checked fusedMap2345swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2345
#print axioms sourceMap2345swap_checked
#print axioms fusedMap2345swap_checked
#print axioms certified2345swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
