/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2172 : Family 8 := level8.get ⟨169,by decide⟩
def sourceMap2172 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2172 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2172_checked : acceptsGraphIso
    (source (graph core2172) (root 8) 0 4) DegreeTwoThreeSpectrum2857.graph sourceMap2172=true := by decide +kernel
theorem fusedMap2172_checked : acceptsGraphIso
    (fused (graph core2172) (root 8) 0 4) DegreeTwoThreeSpectrum2859.graph fusedMap2172=true := by decide +kernel
theorem certified2172 : Certified (graph core2172) (root 8) 0 4 :=
  of_native_maps core2172 DegreeTwoThreeSpectrum2857.graph DegreeTwoThreeSpectrum2859.graph
    sourceMap2172 fusedMap2172 sourceMap2172_checked fusedMap2172_checked
    DegreeTwoThreeFiniteComparisons.comparison2172
#print axioms sourceMap2172_checked
#print axioms fusedMap2172_checked
#print axioms certified2172
def sourceMap2172swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2172swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2172swap_checked : acceptsGraphIso
    (source (graph core2172) (root 8) 4 0) DegreeTwoThreeSpectrum2857.graph sourceMap2172swap=true := by decide +kernel
theorem fusedMap2172swap_checked : acceptsGraphIso
    (fused (graph core2172) (root 8) 4 0) DegreeTwoThreeSpectrum2859.graph fusedMap2172swap=true := by decide +kernel
theorem certified2172swap : Certified (graph core2172) (root 8) 4 0 :=
  of_native_maps core2172 DegreeTwoThreeSpectrum2857.graph DegreeTwoThreeSpectrum2859.graph
    sourceMap2172swap fusedMap2172swap sourceMap2172swap_checked fusedMap2172swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2172
#print axioms sourceMap2172swap_checked
#print axioms fusedMap2172swap_checked
#print axioms certified2172swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
