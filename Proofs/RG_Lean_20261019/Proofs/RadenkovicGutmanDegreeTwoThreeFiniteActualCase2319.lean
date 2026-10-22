/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2319 : Family 9 := level9.get ⟨347,by decide⟩
def sourceMap2319 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2319 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2319_checked : acceptsGraphIso
    (source (graph core2319) (root 9) 0 4) DegreeTwoThreeSpectrum4244.graph sourceMap2319=true := by decide +kernel
theorem fusedMap2319_checked : acceptsGraphIso
    (fused (graph core2319) (root 9) 0 4) DegreeTwoThreeSpectrum4245.graph fusedMap2319=true := by decide +kernel
theorem certified2319 : Certified (graph core2319) (root 9) 0 4 :=
  of_native_maps core2319 DegreeTwoThreeSpectrum4244.graph DegreeTwoThreeSpectrum4245.graph
    sourceMap2319 fusedMap2319 sourceMap2319_checked fusedMap2319_checked
    DegreeTwoThreeFiniteComparisons.comparison2319
#print axioms sourceMap2319_checked
#print axioms fusedMap2319_checked
#print axioms certified2319
def sourceMap2319swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2319swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2319swap_checked : acceptsGraphIso
    (source (graph core2319) (root 9) 4 0) DegreeTwoThreeSpectrum4244.graph sourceMap2319swap=true := by decide +kernel
theorem fusedMap2319swap_checked : acceptsGraphIso
    (fused (graph core2319) (root 9) 4 0) DegreeTwoThreeSpectrum4245.graph fusedMap2319swap=true := by decide +kernel
theorem certified2319swap : Certified (graph core2319) (root 9) 4 0 :=
  of_native_maps core2319 DegreeTwoThreeSpectrum4244.graph DegreeTwoThreeSpectrum4245.graph
    sourceMap2319swap fusedMap2319swap sourceMap2319swap_checked fusedMap2319swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2319
#print axioms sourceMap2319swap_checked
#print axioms fusedMap2319swap_checked
#print axioms certified2319swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
