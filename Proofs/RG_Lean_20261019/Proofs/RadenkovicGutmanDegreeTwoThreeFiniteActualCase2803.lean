/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2803 : Family 10 := level10.get ⟨1082,by decide⟩
def sourceMap2803 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2803 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2803_checked : acceptsGraphIso
    (source (graph core2803) (root 10) 0 4) DegreeTwoThreeSpectrum6146.graph sourceMap2803=true := by decide +kernel
theorem fusedMap2803_checked : acceptsGraphIso
    (fused (graph core2803) (root 10) 0 4) DegreeTwoThreeSpectrum6147.graph fusedMap2803=true := by decide +kernel
theorem certified2803 : Certified (graph core2803) (root 10) 0 4 :=
  of_native_maps core2803 DegreeTwoThreeSpectrum6146.graph DegreeTwoThreeSpectrum6147.graph
    sourceMap2803 fusedMap2803 sourceMap2803_checked fusedMap2803_checked
    DegreeTwoThreeFiniteComparisons.comparison2803
#print axioms sourceMap2803_checked
#print axioms fusedMap2803_checked
#print axioms certified2803
def sourceMap2803swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2803swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2803swap_checked : acceptsGraphIso
    (source (graph core2803) (root 10) 4 0) DegreeTwoThreeSpectrum6146.graph sourceMap2803swap=true := by decide +kernel
theorem fusedMap2803swap_checked : acceptsGraphIso
    (fused (graph core2803) (root 10) 4 0) DegreeTwoThreeSpectrum6147.graph fusedMap2803swap=true := by decide +kernel
theorem certified2803swap : Certified (graph core2803) (root 10) 4 0 :=
  of_native_maps core2803 DegreeTwoThreeSpectrum6146.graph DegreeTwoThreeSpectrum6147.graph
    sourceMap2803swap fusedMap2803swap sourceMap2803swap_checked fusedMap2803swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2803
#print axioms sourceMap2803swap_checked
#print axioms fusedMap2803swap_checked
#print axioms certified2803swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
