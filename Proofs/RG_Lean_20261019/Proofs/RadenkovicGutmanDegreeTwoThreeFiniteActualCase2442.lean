/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2442 : Family 9 := level9.get ⟨650,by decide⟩
def sourceMap2442 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2442 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2442_checked : acceptsGraphIso
    (source (graph core2442) (root 9) 0 4) DegreeTwoThreeSpectrum4814.graph sourceMap2442=true := by decide +kernel
theorem fusedMap2442_checked : acceptsGraphIso
    (fused (graph core2442) (root 9) 0 4) DegreeTwoThreeSpectrum4439.graph fusedMap2442=true := by decide +kernel
theorem certified2442 : Certified (graph core2442) (root 9) 0 4 :=
  of_native_maps core2442 DegreeTwoThreeSpectrum4814.graph DegreeTwoThreeSpectrum4439.graph
    sourceMap2442 fusedMap2442 sourceMap2442_checked fusedMap2442_checked
    DegreeTwoThreeFiniteComparisons.comparison2442
#print axioms sourceMap2442_checked
#print axioms fusedMap2442_checked
#print axioms certified2442
def sourceMap2442swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2442swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2442swap_checked : acceptsGraphIso
    (source (graph core2442) (root 9) 4 0) DegreeTwoThreeSpectrum4814.graph sourceMap2442swap=true := by decide +kernel
theorem fusedMap2442swap_checked : acceptsGraphIso
    (fused (graph core2442) (root 9) 4 0) DegreeTwoThreeSpectrum4439.graph fusedMap2442swap=true := by decide +kernel
theorem certified2442swap : Certified (graph core2442) (root 9) 4 0 :=
  of_native_maps core2442 DegreeTwoThreeSpectrum4814.graph DegreeTwoThreeSpectrum4439.graph
    sourceMap2442swap fusedMap2442swap sourceMap2442swap_checked fusedMap2442swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2442
#print axioms sourceMap2442swap_checked
#print axioms fusedMap2442swap_checked
#print axioms certified2442swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
