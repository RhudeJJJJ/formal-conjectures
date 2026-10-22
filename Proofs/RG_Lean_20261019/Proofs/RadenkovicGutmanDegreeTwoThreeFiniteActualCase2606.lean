/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2606 : Family 10 := level10.get ⟨552,by decide⟩
def sourceMap2606 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2606 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2606_checked : acceptsGraphIso
    (source (graph core2606) (root 10) 0 4) DegreeTwoThreeSpectrum6164.graph sourceMap2606=true := by decide +kernel
theorem fusedMap2606_checked : acceptsGraphIso
    (fused (graph core2606) (root 10) 0 4) DegreeTwoThreeSpectrum5206.graph fusedMap2606=true := by decide +kernel
theorem certified2606 : Certified (graph core2606) (root 10) 0 4 :=
  of_native_maps core2606 DegreeTwoThreeSpectrum6164.graph DegreeTwoThreeSpectrum5206.graph
    sourceMap2606 fusedMap2606 sourceMap2606_checked fusedMap2606_checked
    DegreeTwoThreeFiniteComparisons.comparison2606
#print axioms sourceMap2606_checked
#print axioms fusedMap2606_checked
#print axioms certified2606
def sourceMap2606swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2606swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2606swap_checked : acceptsGraphIso
    (source (graph core2606) (root 10) 4 0) DegreeTwoThreeSpectrum6164.graph sourceMap2606swap=true := by decide +kernel
theorem fusedMap2606swap_checked : acceptsGraphIso
    (fused (graph core2606) (root 10) 4 0) DegreeTwoThreeSpectrum5206.graph fusedMap2606swap=true := by decide +kernel
theorem certified2606swap : Certified (graph core2606) (root 10) 4 0 :=
  of_native_maps core2606 DegreeTwoThreeSpectrum6164.graph DegreeTwoThreeSpectrum5206.graph
    sourceMap2606swap fusedMap2606swap sourceMap2606swap_checked fusedMap2606swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2606
#print axioms sourceMap2606swap_checked
#print axioms fusedMap2606swap_checked
#print axioms certified2606swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
