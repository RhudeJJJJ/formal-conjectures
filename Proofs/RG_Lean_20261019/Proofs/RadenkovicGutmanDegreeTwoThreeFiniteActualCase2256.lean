/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2256 : Family 9 := level9.get ⟨168,by decide⟩
def sourceMap2256 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2256 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2256_checked : acceptsGraphIso
    (source (graph core2256) (root 9) 0 4) DegreeTwoThreeSpectrum4319.graph sourceMap2256=true := by decide +kernel
theorem fusedMap2256_checked : acceptsGraphIso
    (fused (graph core2256) (root 9) 0 4) DegreeTwoThreeSpectrum3930.graph fusedMap2256=true := by decide +kernel
theorem certified2256 : Certified (graph core2256) (root 9) 0 4 :=
  of_native_maps core2256 DegreeTwoThreeSpectrum4319.graph DegreeTwoThreeSpectrum3930.graph
    sourceMap2256 fusedMap2256 sourceMap2256_checked fusedMap2256_checked
    DegreeTwoThreeFiniteComparisons.comparison2256
#print axioms sourceMap2256_checked
#print axioms fusedMap2256_checked
#print axioms certified2256
def sourceMap2256swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2256swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2256swap_checked : acceptsGraphIso
    (source (graph core2256) (root 9) 4 0) DegreeTwoThreeSpectrum4319.graph sourceMap2256swap=true := by decide +kernel
theorem fusedMap2256swap_checked : acceptsGraphIso
    (fused (graph core2256) (root 9) 4 0) DegreeTwoThreeSpectrum3930.graph fusedMap2256swap=true := by decide +kernel
theorem certified2256swap : Certified (graph core2256) (root 9) 4 0 :=
  of_native_maps core2256 DegreeTwoThreeSpectrum4319.graph DegreeTwoThreeSpectrum3930.graph
    sourceMap2256swap fusedMap2256swap sourceMap2256swap_checked fusedMap2256swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2256
#print axioms sourceMap2256swap_checked
#print axioms fusedMap2256swap_checked
#print axioms certified2256swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
