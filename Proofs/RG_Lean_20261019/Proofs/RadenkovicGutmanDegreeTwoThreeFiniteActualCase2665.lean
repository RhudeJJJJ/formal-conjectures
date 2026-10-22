/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2665 : Family 10 := level10.get ⟨721,by decide⟩
def sourceMap2665 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2665 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2665_checked : acceptsGraphIso
    (source (graph core2665) (root 10) 0 4) DegreeTwoThreeSpectrum6578.graph sourceMap2665=true := by decide +kernel
theorem fusedMap2665_checked : acceptsGraphIso
    (fused (graph core2665) (root 10) 0 4) DegreeTwoThreeSpectrum5471.graph fusedMap2665=true := by decide +kernel
theorem certified2665 : Certified (graph core2665) (root 10) 0 4 :=
  of_native_maps core2665 DegreeTwoThreeSpectrum6578.graph DegreeTwoThreeSpectrum5471.graph
    sourceMap2665 fusedMap2665 sourceMap2665_checked fusedMap2665_checked
    DegreeTwoThreeFiniteComparisons.comparison2665
#print axioms sourceMap2665_checked
#print axioms fusedMap2665_checked
#print axioms certified2665
def sourceMap2665swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2665swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2665swap_checked : acceptsGraphIso
    (source (graph core2665) (root 10) 4 0) DegreeTwoThreeSpectrum6578.graph sourceMap2665swap=true := by decide +kernel
theorem fusedMap2665swap_checked : acceptsGraphIso
    (fused (graph core2665) (root 10) 4 0) DegreeTwoThreeSpectrum5471.graph fusedMap2665swap=true := by decide +kernel
theorem certified2665swap : Certified (graph core2665) (root 10) 4 0 :=
  of_native_maps core2665 DegreeTwoThreeSpectrum6578.graph DegreeTwoThreeSpectrum5471.graph
    sourceMap2665swap fusedMap2665swap sourceMap2665swap_checked fusedMap2665swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2665
#print axioms sourceMap2665swap_checked
#print axioms fusedMap2665swap_checked
#print axioms certified2665swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
