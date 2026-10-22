/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2699 : Family 10 := level10.get ⟨817,by decide⟩
def sourceMap2699 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2699 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2699_checked : acceptsGraphIso
    (source (graph core2699) (root 10) 0 4) DegreeTwoThreeSpectrum6779.graph sourceMap2699=true := by decide +kernel
theorem fusedMap2699_checked : acceptsGraphIso
    (fused (graph core2699) (root 10) 0 4) DegreeTwoThreeSpectrum5619.graph fusedMap2699=true := by decide +kernel
theorem certified2699 : Certified (graph core2699) (root 10) 0 4 :=
  of_native_maps core2699 DegreeTwoThreeSpectrum6779.graph DegreeTwoThreeSpectrum5619.graph
    sourceMap2699 fusedMap2699 sourceMap2699_checked fusedMap2699_checked
    DegreeTwoThreeFiniteComparisons.comparison2699
#print axioms sourceMap2699_checked
#print axioms fusedMap2699_checked
#print axioms certified2699
def sourceMap2699swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2699swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2699swap_checked : acceptsGraphIso
    (source (graph core2699) (root 10) 4 0) DegreeTwoThreeSpectrum6779.graph sourceMap2699swap=true := by decide +kernel
theorem fusedMap2699swap_checked : acceptsGraphIso
    (fused (graph core2699) (root 10) 4 0) DegreeTwoThreeSpectrum5619.graph fusedMap2699swap=true := by decide +kernel
theorem certified2699swap : Certified (graph core2699) (root 10) 4 0 :=
  of_native_maps core2699 DegreeTwoThreeSpectrum6779.graph DegreeTwoThreeSpectrum5619.graph
    sourceMap2699swap fusedMap2699swap sourceMap2699swap_checked fusedMap2699swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2699
#print axioms sourceMap2699swap_checked
#print axioms fusedMap2699swap_checked
#print axioms certified2699swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
