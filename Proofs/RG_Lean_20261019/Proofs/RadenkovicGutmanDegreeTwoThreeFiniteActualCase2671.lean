/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2671 : Family 10 := level10.get ⟨742,by decide⟩
def sourceMap2671 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2671 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2671_checked : acceptsGraphIso
    (source (graph core2671) (root 10) 0 4) DegreeTwoThreeSpectrum6638.graph sourceMap2671=true := by decide +kernel
theorem fusedMap2671_checked : acceptsGraphIso
    (fused (graph core2671) (root 10) 0 4) DegreeTwoThreeSpectrum5503.graph fusedMap2671=true := by decide +kernel
theorem certified2671 : Certified (graph core2671) (root 10) 0 4 :=
  of_native_maps core2671 DegreeTwoThreeSpectrum6638.graph DegreeTwoThreeSpectrum5503.graph
    sourceMap2671 fusedMap2671 sourceMap2671_checked fusedMap2671_checked
    DegreeTwoThreeFiniteComparisons.comparison2671
#print axioms sourceMap2671_checked
#print axioms fusedMap2671_checked
#print axioms certified2671
def sourceMap2671swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2671swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2671swap_checked : acceptsGraphIso
    (source (graph core2671) (root 10) 4 0) DegreeTwoThreeSpectrum6638.graph sourceMap2671swap=true := by decide +kernel
theorem fusedMap2671swap_checked : acceptsGraphIso
    (fused (graph core2671) (root 10) 4 0) DegreeTwoThreeSpectrum5503.graph fusedMap2671swap=true := by decide +kernel
theorem certified2671swap : Certified (graph core2671) (root 10) 4 0 :=
  of_native_maps core2671 DegreeTwoThreeSpectrum6638.graph DegreeTwoThreeSpectrum5503.graph
    sourceMap2671swap fusedMap2671swap sourceMap2671swap_checked fusedMap2671swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2671
#print axioms sourceMap2671swap_checked
#print axioms fusedMap2671swap_checked
#print axioms certified2671swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
