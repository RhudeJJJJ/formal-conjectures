/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2694 : Family 10 := level10.get ⟨807,by decide⟩
def sourceMap2694 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2694 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2694_checked : acceptsGraphIso
    (source (graph core2694) (root 10) 0 4) DegreeTwoThreeSpectrum6769.graph sourceMap2694=true := by decide +kernel
theorem fusedMap2694_checked : acceptsGraphIso
    (fused (graph core2694) (root 10) 0 4) DegreeTwoThreeSpectrum5604.graph fusedMap2694=true := by decide +kernel
theorem certified2694 : Certified (graph core2694) (root 10) 0 4 :=
  of_native_maps core2694 DegreeTwoThreeSpectrum6769.graph DegreeTwoThreeSpectrum5604.graph
    sourceMap2694 fusedMap2694 sourceMap2694_checked fusedMap2694_checked
    DegreeTwoThreeFiniteComparisons.comparison2694
#print axioms sourceMap2694_checked
#print axioms fusedMap2694_checked
#print axioms certified2694
def sourceMap2694swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2694swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2694swap_checked : acceptsGraphIso
    (source (graph core2694) (root 10) 4 0) DegreeTwoThreeSpectrum6769.graph sourceMap2694swap=true := by decide +kernel
theorem fusedMap2694swap_checked : acceptsGraphIso
    (fused (graph core2694) (root 10) 4 0) DegreeTwoThreeSpectrum5604.graph fusedMap2694swap=true := by decide +kernel
theorem certified2694swap : Certified (graph core2694) (root 10) 4 0 :=
  of_native_maps core2694 DegreeTwoThreeSpectrum6769.graph DegreeTwoThreeSpectrum5604.graph
    sourceMap2694swap fusedMap2694swap sourceMap2694swap_checked fusedMap2694swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2694
#print axioms sourceMap2694swap_checked
#print axioms fusedMap2694swap_checked
#print axioms certified2694swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
