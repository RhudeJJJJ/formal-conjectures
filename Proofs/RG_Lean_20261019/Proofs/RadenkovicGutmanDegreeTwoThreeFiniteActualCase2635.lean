/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2635 : Family 10 := level10.get ⟨639,by decide⟩
def sourceMap2635 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2635 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2635_checked : acceptsGraphIso
    (source (graph core2635) (root 10) 0 4) DegreeTwoThreeSpectrum6397.graph sourceMap2635=true := by decide +kernel
theorem fusedMap2635_checked : acceptsGraphIso
    (fused (graph core2635) (root 10) 0 4) DegreeTwoThreeSpectrum5334.graph fusedMap2635=true := by decide +kernel
theorem certified2635 : Certified (graph core2635) (root 10) 0 4 :=
  of_native_maps core2635 DegreeTwoThreeSpectrum6397.graph DegreeTwoThreeSpectrum5334.graph
    sourceMap2635 fusedMap2635 sourceMap2635_checked fusedMap2635_checked
    DegreeTwoThreeFiniteComparisons.comparison2635
#print axioms sourceMap2635_checked
#print axioms fusedMap2635_checked
#print axioms certified2635
def sourceMap2635swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2635swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2635swap_checked : acceptsGraphIso
    (source (graph core2635) (root 10) 4 0) DegreeTwoThreeSpectrum6397.graph sourceMap2635swap=true := by decide +kernel
theorem fusedMap2635swap_checked : acceptsGraphIso
    (fused (graph core2635) (root 10) 4 0) DegreeTwoThreeSpectrum5334.graph fusedMap2635swap=true := by decide +kernel
theorem certified2635swap : Certified (graph core2635) (root 10) 4 0 :=
  of_native_maps core2635 DegreeTwoThreeSpectrum6397.graph DegreeTwoThreeSpectrum5334.graph
    sourceMap2635swap fusedMap2635swap sourceMap2635swap_checked fusedMap2635swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2635
#print axioms sourceMap2635swap_checked
#print axioms fusedMap2635swap_checked
#print axioms certified2635swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
