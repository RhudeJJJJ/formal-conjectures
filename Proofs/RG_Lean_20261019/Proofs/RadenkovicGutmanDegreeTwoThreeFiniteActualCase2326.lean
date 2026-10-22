/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2326 : Family 9 := level9.get ⟨364,by decide⟩
def sourceMap2326 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2326 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2326_checked : acceptsGraphIso
    (source (graph core2326) (root 9) 0 4) DegreeTwoThreeSpectrum4282.graph sourceMap2326=true := by decide +kernel
theorem fusedMap2326_checked : acceptsGraphIso
    (fused (graph core2326) (root 9) 0 4) DegreeTwoThreeSpectrum4283.graph fusedMap2326=true := by decide +kernel
theorem certified2326 : Certified (graph core2326) (root 9) 0 4 :=
  of_native_maps core2326 DegreeTwoThreeSpectrum4282.graph DegreeTwoThreeSpectrum4283.graph
    sourceMap2326 fusedMap2326 sourceMap2326_checked fusedMap2326_checked
    DegreeTwoThreeFiniteComparisons.comparison2326
#print axioms sourceMap2326_checked
#print axioms fusedMap2326_checked
#print axioms certified2326
def sourceMap2326swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2326swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2326swap_checked : acceptsGraphIso
    (source (graph core2326) (root 9) 4 0) DegreeTwoThreeSpectrum4282.graph sourceMap2326swap=true := by decide +kernel
theorem fusedMap2326swap_checked : acceptsGraphIso
    (fused (graph core2326) (root 9) 4 0) DegreeTwoThreeSpectrum4283.graph fusedMap2326swap=true := by decide +kernel
theorem certified2326swap : Certified (graph core2326) (root 9) 4 0 :=
  of_native_maps core2326 DegreeTwoThreeSpectrum4282.graph DegreeTwoThreeSpectrum4283.graph
    sourceMap2326swap fusedMap2326swap sourceMap2326swap_checked fusedMap2326swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2326
#print axioms sourceMap2326swap_checked
#print axioms fusedMap2326swap_checked
#print axioms certified2326swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
