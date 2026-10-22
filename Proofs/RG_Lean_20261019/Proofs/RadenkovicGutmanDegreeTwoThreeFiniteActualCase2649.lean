/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2649 : Family 10 := level10.get ⟨674,by decide⟩
def sourceMap2649 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2649 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2649_checked : acceptsGraphIso
    (source (graph core2649) (root 10) 0 4) DegreeTwoThreeSpectrum6463.graph sourceMap2649=true := by decide +kernel
theorem fusedMap2649_checked : acceptsGraphIso
    (fused (graph core2649) (root 10) 0 4) DegreeTwoThreeSpectrum5396.graph fusedMap2649=true := by decide +kernel
theorem certified2649 : Certified (graph core2649) (root 10) 0 4 :=
  of_native_maps core2649 DegreeTwoThreeSpectrum6463.graph DegreeTwoThreeSpectrum5396.graph
    sourceMap2649 fusedMap2649 sourceMap2649_checked fusedMap2649_checked
    DegreeTwoThreeFiniteComparisons.comparison2649
#print axioms sourceMap2649_checked
#print axioms fusedMap2649_checked
#print axioms certified2649
def sourceMap2649swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2649swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2649swap_checked : acceptsGraphIso
    (source (graph core2649) (root 10) 4 0) DegreeTwoThreeSpectrum6463.graph sourceMap2649swap=true := by decide +kernel
theorem fusedMap2649swap_checked : acceptsGraphIso
    (fused (graph core2649) (root 10) 4 0) DegreeTwoThreeSpectrum5396.graph fusedMap2649swap=true := by decide +kernel
theorem certified2649swap : Certified (graph core2649) (root 10) 4 0 :=
  of_native_maps core2649 DegreeTwoThreeSpectrum6463.graph DegreeTwoThreeSpectrum5396.graph
    sourceMap2649swap fusedMap2649swap sourceMap2649swap_checked fusedMap2649swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2649
#print axioms sourceMap2649swap_checked
#print axioms fusedMap2649swap_checked
#print axioms certified2649swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
