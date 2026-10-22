/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2448 : Family 9 := level9.get ⟨667,by decide⟩
def sourceMap2448 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2448 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2448_checked : acceptsGraphIso
    (source (graph core2448) (root 9) 0 4) DegreeTwoThreeSpectrum4842.graph sourceMap2448=true := by decide +kernel
theorem fusedMap2448_checked : acceptsGraphIso
    (fused (graph core2448) (root 9) 0 4) DegreeTwoThreeSpectrum4487.graph fusedMap2448=true := by decide +kernel
theorem certified2448 : Certified (graph core2448) (root 9) 0 4 :=
  of_native_maps core2448 DegreeTwoThreeSpectrum4842.graph DegreeTwoThreeSpectrum4487.graph
    sourceMap2448 fusedMap2448 sourceMap2448_checked fusedMap2448_checked
    DegreeTwoThreeFiniteComparisons.comparison2448
#print axioms sourceMap2448_checked
#print axioms fusedMap2448_checked
#print axioms certified2448
def sourceMap2448swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2448swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2448swap_checked : acceptsGraphIso
    (source (graph core2448) (root 9) 4 0) DegreeTwoThreeSpectrum4842.graph sourceMap2448swap=true := by decide +kernel
theorem fusedMap2448swap_checked : acceptsGraphIso
    (fused (graph core2448) (root 9) 4 0) DegreeTwoThreeSpectrum4487.graph fusedMap2448swap=true := by decide +kernel
theorem certified2448swap : Certified (graph core2448) (root 9) 4 0 :=
  of_native_maps core2448 DegreeTwoThreeSpectrum4842.graph DegreeTwoThreeSpectrum4487.graph
    sourceMap2448swap fusedMap2448swap sourceMap2448swap_checked fusedMap2448swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2448
#print axioms sourceMap2448swap_checked
#print axioms fusedMap2448swap_checked
#print axioms certified2448swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
