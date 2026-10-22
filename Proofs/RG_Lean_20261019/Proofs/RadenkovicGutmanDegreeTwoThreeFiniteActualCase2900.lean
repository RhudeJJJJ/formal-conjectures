/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2900 : Family 10 := level10.get ⟨1322,by decide⟩
def sourceMap2900 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2900 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2900_checked : acceptsGraphIso
    (source (graph core2900) (root 10) 0 4) DegreeTwoThreeSpectrum6631.graph sourceMap2900=true := by decide +kernel
theorem fusedMap2900_checked : acceptsGraphIso
    (fused (graph core2900) (root 10) 0 4) DegreeTwoThreeSpectrum6632.graph fusedMap2900=true := by decide +kernel
theorem certified2900 : Certified (graph core2900) (root 10) 0 4 :=
  of_native_maps core2900 DegreeTwoThreeSpectrum6631.graph DegreeTwoThreeSpectrum6632.graph
    sourceMap2900 fusedMap2900 sourceMap2900_checked fusedMap2900_checked
    DegreeTwoThreeFiniteComparisons.comparison2900
#print axioms sourceMap2900_checked
#print axioms fusedMap2900_checked
#print axioms certified2900
def sourceMap2900swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2900swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2900swap_checked : acceptsGraphIso
    (source (graph core2900) (root 10) 4 0) DegreeTwoThreeSpectrum6631.graph sourceMap2900swap=true := by decide +kernel
theorem fusedMap2900swap_checked : acceptsGraphIso
    (fused (graph core2900) (root 10) 4 0) DegreeTwoThreeSpectrum6632.graph fusedMap2900swap=true := by decide +kernel
theorem certified2900swap : Certified (graph core2900) (root 10) 4 0 :=
  of_native_maps core2900 DegreeTwoThreeSpectrum6631.graph DegreeTwoThreeSpectrum6632.graph
    sourceMap2900swap fusedMap2900swap sourceMap2900swap_checked fusedMap2900swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2900
#print axioms sourceMap2900swap_checked
#print axioms fusedMap2900swap_checked
#print axioms certified2900swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
