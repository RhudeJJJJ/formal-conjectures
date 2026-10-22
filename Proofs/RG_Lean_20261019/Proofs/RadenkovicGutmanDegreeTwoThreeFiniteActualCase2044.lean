/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2044 : Family 10 := level10.get ⟨1751,by decide⟩
def sourceMap2044 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2044 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2044_checked : acceptsGraphIso
    (source (graph core2044) (root 10) 0 2) DegreeTwoThreeSpectrum3842.graph sourceMap2044=true := by decide +kernel
theorem fusedMap2044_checked : acceptsGraphIso
    (fused (graph core2044) (root 10) 0 2) DegreeTwoThreeSpectrum3488.graph fusedMap2044=true := by decide +kernel
theorem certified2044 : Certified (graph core2044) (root 10) 0 2 :=
  of_native_maps core2044 DegreeTwoThreeSpectrum3842.graph DegreeTwoThreeSpectrum3488.graph
    sourceMap2044 fusedMap2044 sourceMap2044_checked fusedMap2044_checked
    DegreeTwoThreeFiniteComparisons.comparison2044
#print axioms sourceMap2044_checked
#print axioms fusedMap2044_checked
#print axioms certified2044
def sourceMap2044swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2044swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2044swap_checked : acceptsGraphIso
    (source (graph core2044) (root 10) 2 0) DegreeTwoThreeSpectrum3842.graph sourceMap2044swap=true := by decide +kernel
theorem fusedMap2044swap_checked : acceptsGraphIso
    (fused (graph core2044) (root 10) 2 0) DegreeTwoThreeSpectrum3488.graph fusedMap2044swap=true := by decide +kernel
theorem certified2044swap : Certified (graph core2044) (root 10) 2 0 :=
  of_native_maps core2044 DegreeTwoThreeSpectrum3842.graph DegreeTwoThreeSpectrum3488.graph
    sourceMap2044swap fusedMap2044swap sourceMap2044swap_checked fusedMap2044swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2044
#print axioms sourceMap2044swap_checked
#print axioms fusedMap2044swap_checked
#print axioms certified2044swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
