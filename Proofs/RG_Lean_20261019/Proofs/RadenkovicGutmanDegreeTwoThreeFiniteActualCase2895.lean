/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2895 : Family 10 := level10.get ⟨1310,by decide⟩
def sourceMap2895 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2895 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2895_checked : acceptsGraphIso
    (source (graph core2895) (root 10) 0 4) DegreeTwoThreeSpectrum6606.graph sourceMap2895=true := by decide +kernel
theorem fusedMap2895_checked : acceptsGraphIso
    (fused (graph core2895) (root 10) 0 4) DegreeTwoThreeSpectrum6607.graph fusedMap2895=true := by decide +kernel
theorem certified2895 : Certified (graph core2895) (root 10) 0 4 :=
  of_native_maps core2895 DegreeTwoThreeSpectrum6606.graph DegreeTwoThreeSpectrum6607.graph
    sourceMap2895 fusedMap2895 sourceMap2895_checked fusedMap2895_checked
    DegreeTwoThreeFiniteComparisons.comparison2895
#print axioms sourceMap2895_checked
#print axioms fusedMap2895_checked
#print axioms certified2895
def sourceMap2895swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2895swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2895swap_checked : acceptsGraphIso
    (source (graph core2895) (root 10) 4 0) DegreeTwoThreeSpectrum6606.graph sourceMap2895swap=true := by decide +kernel
theorem fusedMap2895swap_checked : acceptsGraphIso
    (fused (graph core2895) (root 10) 4 0) DegreeTwoThreeSpectrum6607.graph fusedMap2895swap=true := by decide +kernel
theorem certified2895swap : Certified (graph core2895) (root 10) 4 0 :=
  of_native_maps core2895 DegreeTwoThreeSpectrum6606.graph DegreeTwoThreeSpectrum6607.graph
    sourceMap2895swap fusedMap2895swap sourceMap2895swap_checked fusedMap2895swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2895
#print axioms sourceMap2895swap_checked
#print axioms fusedMap2895swap_checked
#print axioms certified2895swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
