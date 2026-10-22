/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2447 : Family 9 := level9.get ⟨659,by decide⟩
def sourceMap2447 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2447 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2447_checked : acceptsGraphIso
    (source (graph core2447) (root 9) 0 4) DegreeTwoThreeSpectrum4826.graph sourceMap2447=true := by decide +kernel
theorem fusedMap2447_checked : acceptsGraphIso
    (fused (graph core2447) (root 9) 0 4) DegreeTwoThreeSpectrum4459.graph fusedMap2447=true := by decide +kernel
theorem certified2447 : Certified (graph core2447) (root 9) 0 4 :=
  of_native_maps core2447 DegreeTwoThreeSpectrum4826.graph DegreeTwoThreeSpectrum4459.graph
    sourceMap2447 fusedMap2447 sourceMap2447_checked fusedMap2447_checked
    DegreeTwoThreeFiniteComparisons.comparison2447
#print axioms sourceMap2447_checked
#print axioms fusedMap2447_checked
#print axioms certified2447
def sourceMap2447swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2447swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2447swap_checked : acceptsGraphIso
    (source (graph core2447) (root 9) 4 0) DegreeTwoThreeSpectrum4826.graph sourceMap2447swap=true := by decide +kernel
theorem fusedMap2447swap_checked : acceptsGraphIso
    (fused (graph core2447) (root 9) 4 0) DegreeTwoThreeSpectrum4459.graph fusedMap2447swap=true := by decide +kernel
theorem certified2447swap : Certified (graph core2447) (root 9) 4 0 :=
  of_native_maps core2447 DegreeTwoThreeSpectrum4826.graph DegreeTwoThreeSpectrum4459.graph
    sourceMap2447swap fusedMap2447swap sourceMap2447swap_checked fusedMap2447swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2447
#print axioms sourceMap2447swap_checked
#print axioms fusedMap2447swap_checked
#print axioms certified2447swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
