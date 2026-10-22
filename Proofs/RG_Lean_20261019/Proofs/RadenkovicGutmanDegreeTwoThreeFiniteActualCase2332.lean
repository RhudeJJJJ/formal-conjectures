/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2332 : Family 9 := level9.get ⟨380,by decide⟩
def sourceMap2332 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2332 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2332_checked : acceptsGraphIso
    (source (graph core2332) (root 9) 0 4) DegreeTwoThreeSpectrum4316.graph sourceMap2332=true := by decide +kernel
theorem fusedMap2332_checked : acceptsGraphIso
    (fused (graph core2332) (root 9) 0 4) DegreeTwoThreeSpectrum4317.graph fusedMap2332=true := by decide +kernel
theorem certified2332 : Certified (graph core2332) (root 9) 0 4 :=
  of_native_maps core2332 DegreeTwoThreeSpectrum4316.graph DegreeTwoThreeSpectrum4317.graph
    sourceMap2332 fusedMap2332 sourceMap2332_checked fusedMap2332_checked
    DegreeTwoThreeFiniteComparisons.comparison2332
#print axioms sourceMap2332_checked
#print axioms fusedMap2332_checked
#print axioms certified2332
def sourceMap2332swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2332swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2332swap_checked : acceptsGraphIso
    (source (graph core2332) (root 9) 4 0) DegreeTwoThreeSpectrum4316.graph sourceMap2332swap=true := by decide +kernel
theorem fusedMap2332swap_checked : acceptsGraphIso
    (fused (graph core2332) (root 9) 4 0) DegreeTwoThreeSpectrum4317.graph fusedMap2332swap=true := by decide +kernel
theorem certified2332swap : Certified (graph core2332) (root 9) 4 0 :=
  of_native_maps core2332 DegreeTwoThreeSpectrum4316.graph DegreeTwoThreeSpectrum4317.graph
    sourceMap2332swap fusedMap2332swap sourceMap2332swap_checked fusedMap2332swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2332
#print axioms sourceMap2332swap_checked
#print axioms fusedMap2332swap_checked
#print axioms certified2332swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
