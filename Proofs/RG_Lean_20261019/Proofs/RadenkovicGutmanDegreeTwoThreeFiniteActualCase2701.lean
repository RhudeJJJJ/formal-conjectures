/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2701 : Family 10 := level10.get ⟨821,by decide⟩
def sourceMap2701 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2701 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2701_checked : acceptsGraphIso
    (source (graph core2701) (root 10) 0 4) DegreeTwoThreeSpectrum6790.graph sourceMap2701=true := by decide +kernel
theorem fusedMap2701_checked : acceptsGraphIso
    (fused (graph core2701) (root 10) 0 4) DegreeTwoThreeSpectrum5630.graph fusedMap2701=true := by decide +kernel
theorem certified2701 : Certified (graph core2701) (root 10) 0 4 :=
  of_native_maps core2701 DegreeTwoThreeSpectrum6790.graph DegreeTwoThreeSpectrum5630.graph
    sourceMap2701 fusedMap2701 sourceMap2701_checked fusedMap2701_checked
    DegreeTwoThreeFiniteComparisons.comparison2701
#print axioms sourceMap2701_checked
#print axioms fusedMap2701_checked
#print axioms certified2701
def sourceMap2701swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2701swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2701swap_checked : acceptsGraphIso
    (source (graph core2701) (root 10) 4 0) DegreeTwoThreeSpectrum6790.graph sourceMap2701swap=true := by decide +kernel
theorem fusedMap2701swap_checked : acceptsGraphIso
    (fused (graph core2701) (root 10) 4 0) DegreeTwoThreeSpectrum5630.graph fusedMap2701swap=true := by decide +kernel
theorem certified2701swap : Certified (graph core2701) (root 10) 4 0 :=
  of_native_maps core2701 DegreeTwoThreeSpectrum6790.graph DegreeTwoThreeSpectrum5630.graph
    sourceMap2701swap fusedMap2701swap sourceMap2701swap_checked fusedMap2701swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2701
#print axioms sourceMap2701swap_checked
#print axioms fusedMap2701swap_checked
#print axioms certified2701swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
