/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2322 : Family 9 := level9.get ⟨351,by decide⟩
def sourceMap2322 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2322 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2322_checked : acceptsGraphIso
    (source (graph core2322) (root 9) 0 4) DegreeTwoThreeSpectrum4252.graph sourceMap2322=true := by decide +kernel
theorem fusedMap2322_checked : acceptsGraphIso
    (fused (graph core2322) (root 9) 0 4) DegreeTwoThreeSpectrum4253.graph fusedMap2322=true := by decide +kernel
theorem certified2322 : Certified (graph core2322) (root 9) 0 4 :=
  of_native_maps core2322 DegreeTwoThreeSpectrum4252.graph DegreeTwoThreeSpectrum4253.graph
    sourceMap2322 fusedMap2322 sourceMap2322_checked fusedMap2322_checked
    DegreeTwoThreeFiniteComparisons.comparison2322
#print axioms sourceMap2322_checked
#print axioms fusedMap2322_checked
#print axioms certified2322
def sourceMap2322swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2322swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2322swap_checked : acceptsGraphIso
    (source (graph core2322) (root 9) 4 0) DegreeTwoThreeSpectrum4252.graph sourceMap2322swap=true := by decide +kernel
theorem fusedMap2322swap_checked : acceptsGraphIso
    (fused (graph core2322) (root 9) 4 0) DegreeTwoThreeSpectrum4253.graph fusedMap2322swap=true := by decide +kernel
theorem certified2322swap : Certified (graph core2322) (root 9) 4 0 :=
  of_native_maps core2322 DegreeTwoThreeSpectrum4252.graph DegreeTwoThreeSpectrum4253.graph
    sourceMap2322swap fusedMap2322swap sourceMap2322swap_checked fusedMap2322swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2322
#print axioms sourceMap2322swap_checked
#print axioms fusedMap2322swap_checked
#print axioms certified2322swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
