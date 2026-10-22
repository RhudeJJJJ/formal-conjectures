/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2508 : Family 10 := level10.get ⟨238,by decide⟩
def sourceMap2508 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2508 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2508_checked : acceptsGraphIso
    (source (graph core2508) (root 10) 0 4) DegreeTwoThreeSpectrum5301.graph sourceMap2508=true := by decide +kernel
theorem fusedMap2508_checked : acceptsGraphIso
    (fused (graph core2508) (root 10) 0 4) DegreeTwoThreeSpectrum5303.graph fusedMap2508=true := by decide +kernel
theorem certified2508 : Certified (graph core2508) (root 10) 0 4 :=
  of_native_maps core2508 DegreeTwoThreeSpectrum5301.graph DegreeTwoThreeSpectrum5303.graph
    sourceMap2508 fusedMap2508 sourceMap2508_checked fusedMap2508_checked
    DegreeTwoThreeFiniteComparisons.comparison2508
#print axioms sourceMap2508_checked
#print axioms fusedMap2508_checked
#print axioms certified2508
def sourceMap2508swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2508swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2508swap_checked : acceptsGraphIso
    (source (graph core2508) (root 10) 4 0) DegreeTwoThreeSpectrum5301.graph sourceMap2508swap=true := by decide +kernel
theorem fusedMap2508swap_checked : acceptsGraphIso
    (fused (graph core2508) (root 10) 4 0) DegreeTwoThreeSpectrum5303.graph fusedMap2508swap=true := by decide +kernel
theorem certified2508swap : Certified (graph core2508) (root 10) 4 0 :=
  of_native_maps core2508 DegreeTwoThreeSpectrum5301.graph DegreeTwoThreeSpectrum5303.graph
    sourceMap2508swap fusedMap2508swap sourceMap2508swap_checked fusedMap2508swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2508
#print axioms sourceMap2508swap_checked
#print axioms fusedMap2508swap_checked
#print axioms certified2508swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
