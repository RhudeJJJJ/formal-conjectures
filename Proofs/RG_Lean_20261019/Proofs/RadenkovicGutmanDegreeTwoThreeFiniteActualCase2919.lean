/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2919 : Family 10 := level10.get ⟨1364,by decide⟩
def sourceMap2919 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2919 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2919_checked : acceptsGraphIso
    (source (graph core2919) (root 10) 0 4) DegreeTwoThreeSpectrum6701.graph sourceMap2919=true := by decide +kernel
theorem fusedMap2919_checked : acceptsGraphIso
    (fused (graph core2919) (root 10) 0 4) DegreeTwoThreeSpectrum6702.graph fusedMap2919=true := by decide +kernel
theorem certified2919 : Certified (graph core2919) (root 10) 0 4 :=
  of_native_maps core2919 DegreeTwoThreeSpectrum6701.graph DegreeTwoThreeSpectrum6702.graph
    sourceMap2919 fusedMap2919 sourceMap2919_checked fusedMap2919_checked
    DegreeTwoThreeFiniteComparisons.comparison2919
#print axioms sourceMap2919_checked
#print axioms fusedMap2919_checked
#print axioms certified2919
def sourceMap2919swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2919swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2919swap_checked : acceptsGraphIso
    (source (graph core2919) (root 10) 4 0) DegreeTwoThreeSpectrum6701.graph sourceMap2919swap=true := by decide +kernel
theorem fusedMap2919swap_checked : acceptsGraphIso
    (fused (graph core2919) (root 10) 4 0) DegreeTwoThreeSpectrum6702.graph fusedMap2919swap=true := by decide +kernel
theorem certified2919swap : Certified (graph core2919) (root 10) 4 0 :=
  of_native_maps core2919 DegreeTwoThreeSpectrum6701.graph DegreeTwoThreeSpectrum6702.graph
    sourceMap2919swap fusedMap2919swap sourceMap2919swap_checked fusedMap2919swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2919
#print axioms sourceMap2919swap_checked
#print axioms fusedMap2919swap_checked
#print axioms certified2919swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
