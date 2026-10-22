/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2218 : Family 9 := level9.get ⟨28,by decide⟩
def sourceMap2218 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2218 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2218_checked : acceptsGraphIso
    (source (graph core2218) (root 9) 0 4) DegreeTwoThreeSpectrum4112.graph sourceMap2218=true := by decide +kernel
theorem fusedMap2218_checked : acceptsGraphIso
    (fused (graph core2218) (root 9) 0 4) DegreeTwoThreeSpectrum3875.graph fusedMap2218=true := by decide +kernel
theorem certified2218 : Certified (graph core2218) (root 9) 0 4 :=
  of_native_maps core2218 DegreeTwoThreeSpectrum4112.graph DegreeTwoThreeSpectrum3875.graph
    sourceMap2218 fusedMap2218 sourceMap2218_checked fusedMap2218_checked
    DegreeTwoThreeFiniteComparisons.comparison2218
#print axioms sourceMap2218_checked
#print axioms fusedMap2218_checked
#print axioms certified2218
def sourceMap2218swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2218swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2218swap_checked : acceptsGraphIso
    (source (graph core2218) (root 9) 4 0) DegreeTwoThreeSpectrum4112.graph sourceMap2218swap=true := by decide +kernel
theorem fusedMap2218swap_checked : acceptsGraphIso
    (fused (graph core2218) (root 9) 4 0) DegreeTwoThreeSpectrum3875.graph fusedMap2218swap=true := by decide +kernel
theorem certified2218swap : Certified (graph core2218) (root 9) 4 0 :=
  of_native_maps core2218 DegreeTwoThreeSpectrum4112.graph DegreeTwoThreeSpectrum3875.graph
    sourceMap2218swap fusedMap2218swap sourceMap2218swap_checked fusedMap2218swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2218
#print axioms sourceMap2218swap_checked
#print axioms fusedMap2218swap_checked
#print axioms certified2218swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
