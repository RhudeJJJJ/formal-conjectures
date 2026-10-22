/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2640 : Family 10 := level10.get ⟨650,by decide⟩
def sourceMap2640 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2640 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2640_checked : acceptsGraphIso
    (source (graph core2640) (root 10) 0 4) DegreeTwoThreeSpectrum6417.graph sourceMap2640=true := by decide +kernel
theorem fusedMap2640_checked : acceptsGraphIso
    (fused (graph core2640) (root 10) 0 4) DegreeTwoThreeSpectrum5352.graph fusedMap2640=true := by decide +kernel
theorem certified2640 : Certified (graph core2640) (root 10) 0 4 :=
  of_native_maps core2640 DegreeTwoThreeSpectrum6417.graph DegreeTwoThreeSpectrum5352.graph
    sourceMap2640 fusedMap2640 sourceMap2640_checked fusedMap2640_checked
    DegreeTwoThreeFiniteComparisons.comparison2640
#print axioms sourceMap2640_checked
#print axioms fusedMap2640_checked
#print axioms certified2640
def sourceMap2640swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2640swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2640swap_checked : acceptsGraphIso
    (source (graph core2640) (root 10) 4 0) DegreeTwoThreeSpectrum6417.graph sourceMap2640swap=true := by decide +kernel
theorem fusedMap2640swap_checked : acceptsGraphIso
    (fused (graph core2640) (root 10) 4 0) DegreeTwoThreeSpectrum5352.graph fusedMap2640swap=true := by decide +kernel
theorem certified2640swap : Certified (graph core2640) (root 10) 4 0 :=
  of_native_maps core2640 DegreeTwoThreeSpectrum6417.graph DegreeTwoThreeSpectrum5352.graph
    sourceMap2640swap fusedMap2640swap sourceMap2640swap_checked fusedMap2640swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2640
#print axioms sourceMap2640swap_checked
#print axioms fusedMap2640swap_checked
#print axioms certified2640swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
