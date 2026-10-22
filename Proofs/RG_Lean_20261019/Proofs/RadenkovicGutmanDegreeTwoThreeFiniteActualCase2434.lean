/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2434 : Family 9 := level9.get ⟨631,by decide⟩
def sourceMap2434 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2434 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2434_checked : acceptsGraphIso
    (source (graph core2434) (root 9) 0 4) DegreeTwoThreeSpectrum4789.graph sourceMap2434=true := by decide +kernel
theorem fusedMap2434_checked : acceptsGraphIso
    (fused (graph core2434) (root 9) 0 4) DegreeTwoThreeSpectrum4391.graph fusedMap2434=true := by decide +kernel
theorem certified2434 : Certified (graph core2434) (root 9) 0 4 :=
  of_native_maps core2434 DegreeTwoThreeSpectrum4789.graph DegreeTwoThreeSpectrum4391.graph
    sourceMap2434 fusedMap2434 sourceMap2434_checked fusedMap2434_checked
    DegreeTwoThreeFiniteComparisons.comparison2434
#print axioms sourceMap2434_checked
#print axioms fusedMap2434_checked
#print axioms certified2434
def sourceMap2434swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2434swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2434swap_checked : acceptsGraphIso
    (source (graph core2434) (root 9) 4 0) DegreeTwoThreeSpectrum4789.graph sourceMap2434swap=true := by decide +kernel
theorem fusedMap2434swap_checked : acceptsGraphIso
    (fused (graph core2434) (root 9) 4 0) DegreeTwoThreeSpectrum4391.graph fusedMap2434swap=true := by decide +kernel
theorem certified2434swap : Certified (graph core2434) (root 9) 4 0 :=
  of_native_maps core2434 DegreeTwoThreeSpectrum4789.graph DegreeTwoThreeSpectrum4391.graph
    sourceMap2434swap fusedMap2434swap sourceMap2434swap_checked fusedMap2434swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2434
#print axioms sourceMap2434swap_checked
#print axioms fusedMap2434swap_checked
#print axioms certified2434swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
