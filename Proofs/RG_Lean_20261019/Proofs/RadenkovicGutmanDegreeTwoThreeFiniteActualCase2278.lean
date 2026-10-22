/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2278 : Family 9 := level9.get ⟨236,by decide⟩
def sourceMap2278 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2278 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2278_checked : acceptsGraphIso
    (source (graph core2278) (root 9) 0 4) DegreeTwoThreeSpectrum4513.graph sourceMap2278=true := by decide +kernel
theorem fusedMap2278_checked : acceptsGraphIso
    (fused (graph core2278) (root 9) 0 4) DegreeTwoThreeSpectrum4029.graph fusedMap2278=true := by decide +kernel
theorem certified2278 : Certified (graph core2278) (root 9) 0 4 :=
  of_native_maps core2278 DegreeTwoThreeSpectrum4513.graph DegreeTwoThreeSpectrum4029.graph
    sourceMap2278 fusedMap2278 sourceMap2278_checked fusedMap2278_checked
    DegreeTwoThreeFiniteComparisons.comparison2278
#print axioms sourceMap2278_checked
#print axioms fusedMap2278_checked
#print axioms certified2278
def sourceMap2278swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2278swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2278swap_checked : acceptsGraphIso
    (source (graph core2278) (root 9) 4 0) DegreeTwoThreeSpectrum4513.graph sourceMap2278swap=true := by decide +kernel
theorem fusedMap2278swap_checked : acceptsGraphIso
    (fused (graph core2278) (root 9) 4 0) DegreeTwoThreeSpectrum4029.graph fusedMap2278swap=true := by decide +kernel
theorem certified2278swap : Certified (graph core2278) (root 9) 4 0 :=
  of_native_maps core2278 DegreeTwoThreeSpectrum4513.graph DegreeTwoThreeSpectrum4029.graph
    sourceMap2278swap fusedMap2278swap sourceMap2278swap_checked fusedMap2278swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2278
#print axioms sourceMap2278swap_checked
#print axioms fusedMap2278swap_checked
#print axioms certified2278swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
