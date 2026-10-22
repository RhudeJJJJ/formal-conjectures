/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2293 : Family 9 := level9.get ⟨278,by decide⟩
def sourceMap2293 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2293 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2293_checked : acceptsGraphIso
    (source (graph core2293) (root 9) 0 4) DegreeTwoThreeSpectrum4620.graph sourceMap2293=true := by decide +kernel
theorem fusedMap2293_checked : acceptsGraphIso
    (fused (graph core2293) (root 9) 0 4) DegreeTwoThreeSpectrum4095.graph fusedMap2293=true := by decide +kernel
theorem certified2293 : Certified (graph core2293) (root 9) 0 4 :=
  of_native_maps core2293 DegreeTwoThreeSpectrum4620.graph DegreeTwoThreeSpectrum4095.graph
    sourceMap2293 fusedMap2293 sourceMap2293_checked fusedMap2293_checked
    DegreeTwoThreeFiniteComparisons.comparison2293
#print axioms sourceMap2293_checked
#print axioms fusedMap2293_checked
#print axioms certified2293
def sourceMap2293swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2293swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2293swap_checked : acceptsGraphIso
    (source (graph core2293) (root 9) 4 0) DegreeTwoThreeSpectrum4620.graph sourceMap2293swap=true := by decide +kernel
theorem fusedMap2293swap_checked : acceptsGraphIso
    (fused (graph core2293) (root 9) 4 0) DegreeTwoThreeSpectrum4095.graph fusedMap2293swap=true := by decide +kernel
theorem certified2293swap : Certified (graph core2293) (root 9) 4 0 :=
  of_native_maps core2293 DegreeTwoThreeSpectrum4620.graph DegreeTwoThreeSpectrum4095.graph
    sourceMap2293swap fusedMap2293swap sourceMap2293swap_checked fusedMap2293swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2293
#print axioms sourceMap2293swap_checked
#print axioms fusedMap2293swap_checked
#print axioms certified2293swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
