/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2938 : Family 10 := level10.get ⟨1410,by decide⟩
def sourceMap2938 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2938 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2938_checked : acceptsGraphIso
    (source (graph core2938) (root 10) 0 4) DegreeTwoThreeSpectrum6817.graph sourceMap2938=true := by decide +kernel
theorem fusedMap2938_checked : acceptsGraphIso
    (fused (graph core2938) (root 10) 0 4) DegreeTwoThreeSpectrum6818.graph fusedMap2938=true := by decide +kernel
theorem certified2938 : Certified (graph core2938) (root 10) 0 4 :=
  of_native_maps core2938 DegreeTwoThreeSpectrum6817.graph DegreeTwoThreeSpectrum6818.graph
    sourceMap2938 fusedMap2938 sourceMap2938_checked fusedMap2938_checked
    DegreeTwoThreeFiniteComparisons.comparison2938
#print axioms sourceMap2938_checked
#print axioms fusedMap2938_checked
#print axioms certified2938
def sourceMap2938swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2938swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2938swap_checked : acceptsGraphIso
    (source (graph core2938) (root 10) 4 0) DegreeTwoThreeSpectrum6817.graph sourceMap2938swap=true := by decide +kernel
theorem fusedMap2938swap_checked : acceptsGraphIso
    (fused (graph core2938) (root 10) 4 0) DegreeTwoThreeSpectrum6818.graph fusedMap2938swap=true := by decide +kernel
theorem certified2938swap : Certified (graph core2938) (root 10) 4 0 :=
  of_native_maps core2938 DegreeTwoThreeSpectrum6817.graph DegreeTwoThreeSpectrum6818.graph
    sourceMap2938swap fusedMap2938swap sourceMap2938swap_checked fusedMap2938swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2938
#print axioms sourceMap2938swap_checked
#print axioms fusedMap2938swap_checked
#print axioms certified2938swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
