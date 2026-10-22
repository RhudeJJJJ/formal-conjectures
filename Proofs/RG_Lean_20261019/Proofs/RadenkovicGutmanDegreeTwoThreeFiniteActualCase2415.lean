/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2415 : Family 9 := level9.get ⟨578,by decide⟩
def sourceMap2415 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2415 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2415_checked : acceptsGraphIso
    (source (graph core2415) (root 9) 0 4) DegreeTwoThreeSpectrum4709.graph sourceMap2415=true := by decide +kernel
theorem fusedMap2415_checked : acceptsGraphIso
    (fused (graph core2415) (root 9) 0 4) DegreeTwoThreeSpectrum4234.graph fusedMap2415=true := by decide +kernel
theorem certified2415 : Certified (graph core2415) (root 9) 0 4 :=
  of_native_maps core2415 DegreeTwoThreeSpectrum4709.graph DegreeTwoThreeSpectrum4234.graph
    sourceMap2415 fusedMap2415 sourceMap2415_checked fusedMap2415_checked
    DegreeTwoThreeFiniteComparisons.comparison2415
#print axioms sourceMap2415_checked
#print axioms fusedMap2415_checked
#print axioms certified2415
def sourceMap2415swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2415swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2415swap_checked : acceptsGraphIso
    (source (graph core2415) (root 9) 4 0) DegreeTwoThreeSpectrum4709.graph sourceMap2415swap=true := by decide +kernel
theorem fusedMap2415swap_checked : acceptsGraphIso
    (fused (graph core2415) (root 9) 4 0) DegreeTwoThreeSpectrum4234.graph fusedMap2415swap=true := by decide +kernel
theorem certified2415swap : Certified (graph core2415) (root 9) 4 0 :=
  of_native_maps core2415 DegreeTwoThreeSpectrum4709.graph DegreeTwoThreeSpectrum4234.graph
    sourceMap2415swap fusedMap2415swap sourceMap2415swap_checked fusedMap2415swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2415
#print axioms sourceMap2415swap_checked
#print axioms fusedMap2415swap_checked
#print axioms certified2415swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
