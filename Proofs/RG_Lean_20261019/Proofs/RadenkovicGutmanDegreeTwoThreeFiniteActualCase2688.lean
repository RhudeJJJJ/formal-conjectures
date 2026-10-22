/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2688 : Family 10 := level10.get ⟨791,by decide⟩
def sourceMap2688 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2688 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2688_checked : acceptsGraphIso
    (source (graph core2688) (root 10) 0 4) DegreeTwoThreeSpectrum6738.graph sourceMap2688=true := by decide +kernel
theorem fusedMap2688_checked : acceptsGraphIso
    (fused (graph core2688) (root 10) 0 4) DegreeTwoThreeSpectrum5576.graph fusedMap2688=true := by decide +kernel
theorem certified2688 : Certified (graph core2688) (root 10) 0 4 :=
  of_native_maps core2688 DegreeTwoThreeSpectrum6738.graph DegreeTwoThreeSpectrum5576.graph
    sourceMap2688 fusedMap2688 sourceMap2688_checked fusedMap2688_checked
    DegreeTwoThreeFiniteComparisons.comparison2688
#print axioms sourceMap2688_checked
#print axioms fusedMap2688_checked
#print axioms certified2688
def sourceMap2688swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2688swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2688swap_checked : acceptsGraphIso
    (source (graph core2688) (root 10) 4 0) DegreeTwoThreeSpectrum6738.graph sourceMap2688swap=true := by decide +kernel
theorem fusedMap2688swap_checked : acceptsGraphIso
    (fused (graph core2688) (root 10) 4 0) DegreeTwoThreeSpectrum5576.graph fusedMap2688swap=true := by decide +kernel
theorem certified2688swap : Certified (graph core2688) (root 10) 4 0 :=
  of_native_maps core2688 DegreeTwoThreeSpectrum6738.graph DegreeTwoThreeSpectrum5576.graph
    sourceMap2688swap fusedMap2688swap sourceMap2688swap_checked fusedMap2688swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2688
#print axioms sourceMap2688swap_checked
#print axioms fusedMap2688swap_checked
#print axioms certified2688swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
