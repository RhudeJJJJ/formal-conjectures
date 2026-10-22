/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2405 : Family 9 := level9.get ⟨557,by decide⟩
def sourceMap2405 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2405 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2405_checked : acceptsGraphIso
    (source (graph core2405) (root 9) 0 4) DegreeTwoThreeSpectrum4686.graph sourceMap2405=true := by decide +kernel
theorem fusedMap2405_checked : acceptsGraphIso
    (fused (graph core2405) (root 9) 0 4) DegreeTwoThreeSpectrum4193.graph fusedMap2405=true := by decide +kernel
theorem certified2405 : Certified (graph core2405) (root 9) 0 4 :=
  of_native_maps core2405 DegreeTwoThreeSpectrum4686.graph DegreeTwoThreeSpectrum4193.graph
    sourceMap2405 fusedMap2405 sourceMap2405_checked fusedMap2405_checked
    DegreeTwoThreeFiniteComparisons.comparison2405
#print axioms sourceMap2405_checked
#print axioms fusedMap2405_checked
#print axioms certified2405
def sourceMap2405swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2405swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2405swap_checked : acceptsGraphIso
    (source (graph core2405) (root 9) 4 0) DegreeTwoThreeSpectrum4686.graph sourceMap2405swap=true := by decide +kernel
theorem fusedMap2405swap_checked : acceptsGraphIso
    (fused (graph core2405) (root 9) 4 0) DegreeTwoThreeSpectrum4193.graph fusedMap2405swap=true := by decide +kernel
theorem certified2405swap : Certified (graph core2405) (root 9) 4 0 :=
  of_native_maps core2405 DegreeTwoThreeSpectrum4686.graph DegreeTwoThreeSpectrum4193.graph
    sourceMap2405swap fusedMap2405swap sourceMap2405swap_checked fusedMap2405swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2405
#print axioms sourceMap2405swap_checked
#print axioms fusedMap2405swap_checked
#print axioms certified2405swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
