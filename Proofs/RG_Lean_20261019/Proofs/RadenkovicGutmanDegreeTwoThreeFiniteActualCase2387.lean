/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2387 : Family 9 := level9.get ⟨511,by decide⟩
def sourceMap2387 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2387 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2387_checked : acceptsGraphIso
    (source (graph core2387) (root 9) 0 4) DegreeTwoThreeSpectrum4595.graph sourceMap2387=true := by decide +kernel
theorem fusedMap2387_checked : acceptsGraphIso
    (fused (graph core2387) (root 9) 0 4) DegreeTwoThreeSpectrum4596.graph fusedMap2387=true := by decide +kernel
theorem certified2387 : Certified (graph core2387) (root 9) 0 4 :=
  of_native_maps core2387 DegreeTwoThreeSpectrum4595.graph DegreeTwoThreeSpectrum4596.graph
    sourceMap2387 fusedMap2387 sourceMap2387_checked fusedMap2387_checked
    DegreeTwoThreeFiniteComparisons.comparison2387
#print axioms sourceMap2387_checked
#print axioms fusedMap2387_checked
#print axioms certified2387
def sourceMap2387swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2387swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2387swap_checked : acceptsGraphIso
    (source (graph core2387) (root 9) 4 0) DegreeTwoThreeSpectrum4595.graph sourceMap2387swap=true := by decide +kernel
theorem fusedMap2387swap_checked : acceptsGraphIso
    (fused (graph core2387) (root 9) 4 0) DegreeTwoThreeSpectrum4596.graph fusedMap2387swap=true := by decide +kernel
theorem certified2387swap : Certified (graph core2387) (root 9) 4 0 :=
  of_native_maps core2387 DegreeTwoThreeSpectrum4595.graph DegreeTwoThreeSpectrum4596.graph
    sourceMap2387swap fusedMap2387swap sourceMap2387swap_checked fusedMap2387swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2387
#print axioms sourceMap2387swap_checked
#print axioms fusedMap2387swap_checked
#print axioms certified2387swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
