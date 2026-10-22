/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2192 : Family 8 := level8.get ⟨215,by decide⟩
def sourceMap2192 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2192 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2192_checked : acceptsGraphIso
    (source (graph core2192) (root 8) 0 4) DegreeTwoThreeSpectrum3211.graph sourceMap2192=true := by decide +kernel
theorem fusedMap2192_checked : acceptsGraphIso
    (fused (graph core2192) (root 8) 0 4) DegreeTwoThreeSpectrum2520.graph fusedMap2192=true := by decide +kernel
theorem certified2192 : Certified (graph core2192) (root 8) 0 4 :=
  of_native_maps core2192 DegreeTwoThreeSpectrum3211.graph DegreeTwoThreeSpectrum2520.graph
    sourceMap2192 fusedMap2192 sourceMap2192_checked fusedMap2192_checked
    DegreeTwoThreeFiniteComparisons.comparison2192
#print axioms sourceMap2192_checked
#print axioms fusedMap2192_checked
#print axioms certified2192
def sourceMap2192swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2192swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2192swap_checked : acceptsGraphIso
    (source (graph core2192) (root 8) 4 0) DegreeTwoThreeSpectrum3211.graph sourceMap2192swap=true := by decide +kernel
theorem fusedMap2192swap_checked : acceptsGraphIso
    (fused (graph core2192) (root 8) 4 0) DegreeTwoThreeSpectrum2520.graph fusedMap2192swap=true := by decide +kernel
theorem certified2192swap : Certified (graph core2192) (root 8) 4 0 :=
  of_native_maps core2192 DegreeTwoThreeSpectrum3211.graph DegreeTwoThreeSpectrum2520.graph
    sourceMap2192swap fusedMap2192swap sourceMap2192swap_checked fusedMap2192swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2192
#print axioms sourceMap2192swap_checked
#print axioms fusedMap2192swap_checked
#print axioms certified2192swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
