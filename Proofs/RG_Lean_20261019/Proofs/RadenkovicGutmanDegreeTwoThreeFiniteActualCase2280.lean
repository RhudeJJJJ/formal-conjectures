/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2280 : Family 9 := level9.get ⟨242,by decide⟩
def sourceMap2280 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2280 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2280_checked : acceptsGraphIso
    (source (graph core2280) (root 9) 0 4) DegreeTwoThreeSpectrum4529.graph sourceMap2280=true := by decide +kernel
theorem fusedMap2280_checked : acceptsGraphIso
    (fused (graph core2280) (root 9) 0 4) DegreeTwoThreeSpectrum4039.graph fusedMap2280=true := by decide +kernel
theorem certified2280 : Certified (graph core2280) (root 9) 0 4 :=
  of_native_maps core2280 DegreeTwoThreeSpectrum4529.graph DegreeTwoThreeSpectrum4039.graph
    sourceMap2280 fusedMap2280 sourceMap2280_checked fusedMap2280_checked
    DegreeTwoThreeFiniteComparisons.comparison2280
#print axioms sourceMap2280_checked
#print axioms fusedMap2280_checked
#print axioms certified2280
def sourceMap2280swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2280swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2280swap_checked : acceptsGraphIso
    (source (graph core2280) (root 9) 4 0) DegreeTwoThreeSpectrum4529.graph sourceMap2280swap=true := by decide +kernel
theorem fusedMap2280swap_checked : acceptsGraphIso
    (fused (graph core2280) (root 9) 4 0) DegreeTwoThreeSpectrum4039.graph fusedMap2280swap=true := by decide +kernel
theorem certified2280swap : Certified (graph core2280) (root 9) 4 0 :=
  of_native_maps core2280 DegreeTwoThreeSpectrum4529.graph DegreeTwoThreeSpectrum4039.graph
    sourceMap2280swap fusedMap2280swap sourceMap2280swap_checked fusedMap2280swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2280
#print axioms sourceMap2280swap_checked
#print axioms fusedMap2280swap_checked
#print axioms certified2280swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
