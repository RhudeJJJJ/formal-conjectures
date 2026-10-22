/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2546 : Family 10 := level10.get ⟨364,by decide⟩
def sourceMap2546 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2546 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 0 4 v)
theorem sourceMap2546_checked : acceptsGraphIso
    (source (graph core2546) (root 10) 0 4) DegreeTwoThreeSpectrum5649.graph sourceMap2546=true := by decide +kernel
theorem fusedMap2546_checked : acceptsGraphIso
    (fused (graph core2546) (root 10) 0 4) DegreeTwoThreeSpectrum5653.graph fusedMap2546=true := by decide +kernel
theorem certified2546 : Certified (graph core2546) (root 10) 0 4 :=
  of_native_maps core2546 DegreeTwoThreeSpectrum5649.graph DegreeTwoThreeSpectrum5653.graph
    sourceMap2546 fusedMap2546 sourceMap2546_checked fusedMap2546_checked
    DegreeTwoThreeFiniteComparisons.comparison2546
#print axioms sourceMap2546_checked
#print axioms fusedMap2546_checked
#print axioms certified2546
def sourceMap2546swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2546swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 4 0 v)
theorem sourceMap2546swap_checked : acceptsGraphIso
    (source (graph core2546) (root 10) 4 0) DegreeTwoThreeSpectrum5649.graph sourceMap2546swap=true := by decide +kernel
theorem fusedMap2546swap_checked : acceptsGraphIso
    (fused (graph core2546) (root 10) 4 0) DegreeTwoThreeSpectrum5653.graph fusedMap2546swap=true := by decide +kernel
theorem certified2546swap : Certified (graph core2546) (root 10) 4 0 :=
  of_native_maps core2546 DegreeTwoThreeSpectrum5649.graph DegreeTwoThreeSpectrum5653.graph
    sourceMap2546swap fusedMap2546swap sourceMap2546swap_checked fusedMap2546swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2546
#print axioms sourceMap2546swap_checked
#print axioms fusedMap2546swap_checked
#print axioms certified2546swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
