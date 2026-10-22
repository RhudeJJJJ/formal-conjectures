/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2433 : Family 9 := level9.get ⟨622,by decide⟩
def sourceMap2433 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2433 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2433_checked : acceptsGraphIso
    (source (graph core2433) (root 9) 0 4) DegreeTwoThreeSpectrum4768.graph sourceMap2433=true := by decide +kernel
theorem fusedMap2433_checked : acceptsGraphIso
    (fused (graph core2433) (root 9) 0 4) DegreeTwoThreeSpectrum4339.graph fusedMap2433=true := by decide +kernel
theorem certified2433 : Certified (graph core2433) (root 9) 0 4 :=
  of_native_maps core2433 DegreeTwoThreeSpectrum4768.graph DegreeTwoThreeSpectrum4339.graph
    sourceMap2433 fusedMap2433 sourceMap2433_checked fusedMap2433_checked
    DegreeTwoThreeFiniteComparisons.comparison2433
#print axioms sourceMap2433_checked
#print axioms fusedMap2433_checked
#print axioms certified2433
def sourceMap2433swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2433swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2433swap_checked : acceptsGraphIso
    (source (graph core2433) (root 9) 4 0) DegreeTwoThreeSpectrum4768.graph sourceMap2433swap=true := by decide +kernel
theorem fusedMap2433swap_checked : acceptsGraphIso
    (fused (graph core2433) (root 9) 4 0) DegreeTwoThreeSpectrum4339.graph fusedMap2433swap=true := by decide +kernel
theorem certified2433swap : Certified (graph core2433) (root 9) 4 0 :=
  of_native_maps core2433 DegreeTwoThreeSpectrum4768.graph DegreeTwoThreeSpectrum4339.graph
    sourceMap2433swap fusedMap2433swap sourceMap2433swap_checked fusedMap2433swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2433
#print axioms sourceMap2433swap_checked
#print axioms fusedMap2433swap_checked
#print axioms certified2433swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
