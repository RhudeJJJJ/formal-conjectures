/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2143 : Family 8 := level8.get ⟨91,by decide⟩
def sourceMap2143 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,6,7,8,9,10] (sourceLabel 8 0 4 v)
def fusedMap2143 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2143_checked : acceptsGraphIso
    (source (graph core2143) (root 8) 0 4) DegreeTwoThreeSpectrum2994.graph sourceMap2143=true := by decide +kernel
theorem fusedMap2143_checked : acceptsGraphIso
    (fused (graph core2143) (root 8) 0 4) DegreeTwoThreeSpectrum2428.graph fusedMap2143=true := by decide +kernel
theorem certified2143 : Certified (graph core2143) (root 8) 0 4 :=
  of_native_maps core2143 DegreeTwoThreeSpectrum2994.graph DegreeTwoThreeSpectrum2428.graph
    sourceMap2143 fusedMap2143 sourceMap2143_checked fusedMap2143_checked
    DegreeTwoThreeFiniteComparisons.comparison2143
#print axioms sourceMap2143_checked
#print axioms fusedMap2143_checked
#print axioms certified2143
def sourceMap2143swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,11,12,13,6,7,8,9,10,14] (sourceLabel 8 4 0 v)
def fusedMap2143swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2143swap_checked : acceptsGraphIso
    (source (graph core2143) (root 8) 4 0) DegreeTwoThreeSpectrum2994.graph sourceMap2143swap=true := by decide +kernel
theorem fusedMap2143swap_checked : acceptsGraphIso
    (fused (graph core2143) (root 8) 4 0) DegreeTwoThreeSpectrum2428.graph fusedMap2143swap=true := by decide +kernel
theorem certified2143swap : Certified (graph core2143) (root 8) 4 0 :=
  of_native_maps core2143 DegreeTwoThreeSpectrum2994.graph DegreeTwoThreeSpectrum2428.graph
    sourceMap2143swap fusedMap2143swap sourceMap2143swap_checked fusedMap2143swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2143
#print axioms sourceMap2143swap_checked
#print axioms fusedMap2143swap_checked
#print axioms certified2143swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
