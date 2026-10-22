/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2394 : Family 9 := level9.get ⟨527,by decide⟩
def sourceMap2394 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2394 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2394_checked : acceptsGraphIso
    (source (graph core2394) (root 9) 0 4) DegreeTwoThreeSpectrum4628.graph sourceMap2394=true := by decide +kernel
theorem fusedMap2394_checked : acceptsGraphIso
    (fused (graph core2394) (root 9) 0 4) DegreeTwoThreeSpectrum4629.graph fusedMap2394=true := by decide +kernel
theorem certified2394 : Certified (graph core2394) (root 9) 0 4 :=
  of_native_maps core2394 DegreeTwoThreeSpectrum4628.graph DegreeTwoThreeSpectrum4629.graph
    sourceMap2394 fusedMap2394 sourceMap2394_checked fusedMap2394_checked
    DegreeTwoThreeFiniteComparisons.comparison2394
#print axioms sourceMap2394_checked
#print axioms fusedMap2394_checked
#print axioms certified2394
def sourceMap2394swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2394swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2394swap_checked : acceptsGraphIso
    (source (graph core2394) (root 9) 4 0) DegreeTwoThreeSpectrum4628.graph sourceMap2394swap=true := by decide +kernel
theorem fusedMap2394swap_checked : acceptsGraphIso
    (fused (graph core2394) (root 9) 4 0) DegreeTwoThreeSpectrum4629.graph fusedMap2394swap=true := by decide +kernel
theorem certified2394swap : Certified (graph core2394) (root 9) 4 0 :=
  of_native_maps core2394 DegreeTwoThreeSpectrum4628.graph DegreeTwoThreeSpectrum4629.graph
    sourceMap2394swap fusedMap2394swap sourceMap2394swap_checked fusedMap2394swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2394
#print axioms sourceMap2394swap_checked
#print axioms fusedMap2394swap_checked
#print axioms certified2394swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
