/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2791 : Family 10 := level10.get ⟨1056,by decide⟩
def sourceMap2791 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2791 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2791_checked : acceptsGraphIso
    (source (graph core2791) (root 10) 0 4) DegreeTwoThreeSpectrum6098.graph sourceMap2791=true := by decide +kernel
theorem fusedMap2791_checked : acceptsGraphIso
    (fused (graph core2791) (root 10) 0 4) DegreeTwoThreeSpectrum6099.graph fusedMap2791=true := by decide +kernel
theorem certified2791 : Certified (graph core2791) (root 10) 0 4 :=
  of_native_maps core2791 DegreeTwoThreeSpectrum6098.graph DegreeTwoThreeSpectrum6099.graph
    sourceMap2791 fusedMap2791 sourceMap2791_checked fusedMap2791_checked
    DegreeTwoThreeFiniteComparisons.comparison2791
#print axioms sourceMap2791_checked
#print axioms fusedMap2791_checked
#print axioms certified2791
def sourceMap2791swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2791swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2791swap_checked : acceptsGraphIso
    (source (graph core2791) (root 10) 4 0) DegreeTwoThreeSpectrum6098.graph sourceMap2791swap=true := by decide +kernel
theorem fusedMap2791swap_checked : acceptsGraphIso
    (fused (graph core2791) (root 10) 4 0) DegreeTwoThreeSpectrum6099.graph fusedMap2791swap=true := by decide +kernel
theorem certified2791swap : Certified (graph core2791) (root 10) 4 0 :=
  of_native_maps core2791 DegreeTwoThreeSpectrum6098.graph DegreeTwoThreeSpectrum6099.graph
    sourceMap2791swap fusedMap2791swap sourceMap2791swap_checked fusedMap2791swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2791
#print axioms sourceMap2791swap_checked
#print axioms fusedMap2791swap_checked
#print axioms certified2791swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
