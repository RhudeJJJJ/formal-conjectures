/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2384 : Family 9 := level9.get ⟨505,by decide⟩
def sourceMap2384 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2384 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2384_checked : acceptsGraphIso
    (source (graph core2384) (root 9) 0 4) DegreeTwoThreeSpectrum4585.graph sourceMap2384=true := by decide +kernel
theorem fusedMap2384_checked : acceptsGraphIso
    (fused (graph core2384) (root 9) 0 4) DegreeTwoThreeSpectrum4586.graph fusedMap2384=true := by decide +kernel
theorem certified2384 : Certified (graph core2384) (root 9) 0 4 :=
  of_native_maps core2384 DegreeTwoThreeSpectrum4585.graph DegreeTwoThreeSpectrum4586.graph
    sourceMap2384 fusedMap2384 sourceMap2384_checked fusedMap2384_checked
    DegreeTwoThreeFiniteComparisons.comparison2384
#print axioms sourceMap2384_checked
#print axioms fusedMap2384_checked
#print axioms certified2384
def sourceMap2384swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2384swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2384swap_checked : acceptsGraphIso
    (source (graph core2384) (root 9) 4 0) DegreeTwoThreeSpectrum4585.graph sourceMap2384swap=true := by decide +kernel
theorem fusedMap2384swap_checked : acceptsGraphIso
    (fused (graph core2384) (root 9) 4 0) DegreeTwoThreeSpectrum4586.graph fusedMap2384swap=true := by decide +kernel
theorem certified2384swap : Certified (graph core2384) (root 9) 4 0 :=
  of_native_maps core2384 DegreeTwoThreeSpectrum4585.graph DegreeTwoThreeSpectrum4586.graph
    sourceMap2384swap fusedMap2384swap sourceMap2384swap_checked fusedMap2384swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2384
#print axioms sourceMap2384swap_checked
#print axioms fusedMap2384swap_checked
#print axioms certified2384swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
