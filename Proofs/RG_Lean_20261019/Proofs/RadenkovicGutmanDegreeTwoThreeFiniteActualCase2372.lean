/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2372 : Family 9 := level9.get ⟨477,by decide⟩
def sourceMap2372 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2372 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2372_checked : acceptsGraphIso
    (source (graph core2372) (root 9) 0 4) DegreeTwoThreeSpectrum4516.graph sourceMap2372=true := by decide +kernel
theorem fusedMap2372_checked : acceptsGraphIso
    (fused (graph core2372) (root 9) 0 4) DegreeTwoThreeSpectrum4517.graph fusedMap2372=true := by decide +kernel
theorem certified2372 : Certified (graph core2372) (root 9) 0 4 :=
  of_native_maps core2372 DegreeTwoThreeSpectrum4516.graph DegreeTwoThreeSpectrum4517.graph
    sourceMap2372 fusedMap2372 sourceMap2372_checked fusedMap2372_checked
    DegreeTwoThreeFiniteComparisons.comparison2372
#print axioms sourceMap2372_checked
#print axioms fusedMap2372_checked
#print axioms certified2372
def sourceMap2372swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2372swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2372swap_checked : acceptsGraphIso
    (source (graph core2372) (root 9) 4 0) DegreeTwoThreeSpectrum4516.graph sourceMap2372swap=true := by decide +kernel
theorem fusedMap2372swap_checked : acceptsGraphIso
    (fused (graph core2372) (root 9) 4 0) DegreeTwoThreeSpectrum4517.graph fusedMap2372swap=true := by decide +kernel
theorem certified2372swap : Certified (graph core2372) (root 9) 4 0 :=
  of_native_maps core2372 DegreeTwoThreeSpectrum4516.graph DegreeTwoThreeSpectrum4517.graph
    sourceMap2372swap fusedMap2372swap sourceMap2372swap_checked fusedMap2372swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2372
#print axioms sourceMap2372swap_checked
#print axioms fusedMap2372swap_checked
#print axioms certified2372swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
