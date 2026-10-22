/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2397 : Family 9 := level9.get ⟨531,by decide⟩
def sourceMap2397 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2397 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2397_checked : acceptsGraphIso
    (source (graph core2397) (root 9) 0 4) DegreeTwoThreeSpectrum4636.graph sourceMap2397=true := by decide +kernel
theorem fusedMap2397_checked : acceptsGraphIso
    (fused (graph core2397) (root 9) 0 4) DegreeTwoThreeSpectrum4637.graph fusedMap2397=true := by decide +kernel
theorem certified2397 : Certified (graph core2397) (root 9) 0 4 :=
  of_native_maps core2397 DegreeTwoThreeSpectrum4636.graph DegreeTwoThreeSpectrum4637.graph
    sourceMap2397 fusedMap2397 sourceMap2397_checked fusedMap2397_checked
    DegreeTwoThreeFiniteComparisons.comparison2397
#print axioms sourceMap2397_checked
#print axioms fusedMap2397_checked
#print axioms certified2397
def sourceMap2397swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2397swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2397swap_checked : acceptsGraphIso
    (source (graph core2397) (root 9) 4 0) DegreeTwoThreeSpectrum4636.graph sourceMap2397swap=true := by decide +kernel
theorem fusedMap2397swap_checked : acceptsGraphIso
    (fused (graph core2397) (root 9) 4 0) DegreeTwoThreeSpectrum4637.graph fusedMap2397swap=true := by decide +kernel
theorem certified2397swap : Certified (graph core2397) (root 9) 4 0 :=
  of_native_maps core2397 DegreeTwoThreeSpectrum4636.graph DegreeTwoThreeSpectrum4637.graph
    sourceMap2397swap fusedMap2397swap sourceMap2397swap_checked fusedMap2397swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2397
#print axioms sourceMap2397swap_checked
#print axioms fusedMap2397swap_checked
#print axioms certified2397swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
