/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2420 : Family 9 := level9.get ⟨593,by decide⟩
def sourceMap2420 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2420 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2420_checked : acceptsGraphIso
    (source (graph core2420) (root 9) 0 4) DegreeTwoThreeSpectrum4726.graph sourceMap2420=true := by decide +kernel
theorem fusedMap2420_checked : acceptsGraphIso
    (fused (graph core2420) (root 9) 0 4) DegreeTwoThreeSpectrum4269.graph fusedMap2420=true := by decide +kernel
theorem certified2420 : Certified (graph core2420) (root 9) 0 4 :=
  of_native_maps core2420 DegreeTwoThreeSpectrum4726.graph DegreeTwoThreeSpectrum4269.graph
    sourceMap2420 fusedMap2420 sourceMap2420_checked fusedMap2420_checked
    DegreeTwoThreeFiniteComparisons.comparison2420
#print axioms sourceMap2420_checked
#print axioms fusedMap2420_checked
#print axioms certified2420
def sourceMap2420swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2420swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2420swap_checked : acceptsGraphIso
    (source (graph core2420) (root 9) 4 0) DegreeTwoThreeSpectrum4726.graph sourceMap2420swap=true := by decide +kernel
theorem fusedMap2420swap_checked : acceptsGraphIso
    (fused (graph core2420) (root 9) 4 0) DegreeTwoThreeSpectrum4269.graph fusedMap2420swap=true := by decide +kernel
theorem certified2420swap : Certified (graph core2420) (root 9) 4 0 :=
  of_native_maps core2420 DegreeTwoThreeSpectrum4726.graph DegreeTwoThreeSpectrum4269.graph
    sourceMap2420swap fusedMap2420swap sourceMap2420swap_checked fusedMap2420swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2420
#print axioms sourceMap2420swap_checked
#print axioms fusedMap2420swap_checked
#print axioms certified2420swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
