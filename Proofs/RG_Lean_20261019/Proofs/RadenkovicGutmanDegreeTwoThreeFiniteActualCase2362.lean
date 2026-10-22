/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2362 : Family 9 := level9.get ⟨454,by decide⟩
def sourceMap2362 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2362 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2362_checked : acceptsGraphIso
    (source (graph core2362) (root 9) 0 4) DegreeTwoThreeSpectrum4472.graph sourceMap2362=true := by decide +kernel
theorem fusedMap2362_checked : acceptsGraphIso
    (fused (graph core2362) (root 9) 0 4) DegreeTwoThreeSpectrum4473.graph fusedMap2362=true := by decide +kernel
theorem certified2362 : Certified (graph core2362) (root 9) 0 4 :=
  of_native_maps core2362 DegreeTwoThreeSpectrum4472.graph DegreeTwoThreeSpectrum4473.graph
    sourceMap2362 fusedMap2362 sourceMap2362_checked fusedMap2362_checked
    DegreeTwoThreeFiniteComparisons.comparison2362
#print axioms sourceMap2362_checked
#print axioms fusedMap2362_checked
#print axioms certified2362
def sourceMap2362swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2362swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2362swap_checked : acceptsGraphIso
    (source (graph core2362) (root 9) 4 0) DegreeTwoThreeSpectrum4472.graph sourceMap2362swap=true := by decide +kernel
theorem fusedMap2362swap_checked : acceptsGraphIso
    (fused (graph core2362) (root 9) 4 0) DegreeTwoThreeSpectrum4473.graph fusedMap2362swap=true := by decide +kernel
theorem certified2362swap : Certified (graph core2362) (root 9) 4 0 :=
  of_native_maps core2362 DegreeTwoThreeSpectrum4472.graph DegreeTwoThreeSpectrum4473.graph
    sourceMap2362swap fusedMap2362swap sourceMap2362swap_checked fusedMap2362swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2362
#print axioms sourceMap2362swap_checked
#print axioms fusedMap2362swap_checked
#print axioms certified2362swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
