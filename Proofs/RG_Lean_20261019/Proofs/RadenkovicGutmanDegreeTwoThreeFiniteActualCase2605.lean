/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2605 : Family 10 := level10.get ⟨550,by decide⟩
def sourceMap2605 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2605 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2605_checked : acceptsGraphIso
    (source (graph core2605) (root 10) 0 4) DegreeTwoThreeSpectrum6163.graph sourceMap2605=true := by decide +kernel
theorem fusedMap2605_checked : acceptsGraphIso
    (fused (graph core2605) (root 10) 0 4) DegreeTwoThreeSpectrum5204.graph fusedMap2605=true := by decide +kernel
theorem certified2605 : Certified (graph core2605) (root 10) 0 4 :=
  of_native_maps core2605 DegreeTwoThreeSpectrum6163.graph DegreeTwoThreeSpectrum5204.graph
    sourceMap2605 fusedMap2605 sourceMap2605_checked fusedMap2605_checked
    DegreeTwoThreeFiniteComparisons.comparison2605
#print axioms sourceMap2605_checked
#print axioms fusedMap2605_checked
#print axioms certified2605
def sourceMap2605swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2605swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2605swap_checked : acceptsGraphIso
    (source (graph core2605) (root 10) 4 0) DegreeTwoThreeSpectrum6163.graph sourceMap2605swap=true := by decide +kernel
theorem fusedMap2605swap_checked : acceptsGraphIso
    (fused (graph core2605) (root 10) 4 0) DegreeTwoThreeSpectrum5204.graph fusedMap2605swap=true := by decide +kernel
theorem certified2605swap : Certified (graph core2605) (root 10) 4 0 :=
  of_native_maps core2605 DegreeTwoThreeSpectrum6163.graph DegreeTwoThreeSpectrum5204.graph
    sourceMap2605swap fusedMap2605swap sourceMap2605swap_checked fusedMap2605swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2605
#print axioms sourceMap2605swap_checked
#print axioms fusedMap2605swap_checked
#print axioms certified2605swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
