/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2801 : Family 10 := level10.get ⟨1079,by decide⟩
def sourceMap2801 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2801 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2801_checked : acceptsGraphIso
    (source (graph core2801) (root 10) 0 4) DegreeTwoThreeSpectrum6140.graph sourceMap2801=true := by decide +kernel
theorem fusedMap2801_checked : acceptsGraphIso
    (fused (graph core2801) (root 10) 0 4) DegreeTwoThreeSpectrum6141.graph fusedMap2801=true := by decide +kernel
theorem certified2801 : Certified (graph core2801) (root 10) 0 4 :=
  of_native_maps core2801 DegreeTwoThreeSpectrum6140.graph DegreeTwoThreeSpectrum6141.graph
    sourceMap2801 fusedMap2801 sourceMap2801_checked fusedMap2801_checked
    DegreeTwoThreeFiniteComparisons.comparison2801
#print axioms sourceMap2801_checked
#print axioms fusedMap2801_checked
#print axioms certified2801
def sourceMap2801swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2801swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2801swap_checked : acceptsGraphIso
    (source (graph core2801) (root 10) 4 0) DegreeTwoThreeSpectrum6140.graph sourceMap2801swap=true := by decide +kernel
theorem fusedMap2801swap_checked : acceptsGraphIso
    (fused (graph core2801) (root 10) 4 0) DegreeTwoThreeSpectrum6141.graph fusedMap2801swap=true := by decide +kernel
theorem certified2801swap : Certified (graph core2801) (root 10) 4 0 :=
  of_native_maps core2801 DegreeTwoThreeSpectrum6140.graph DegreeTwoThreeSpectrum6141.graph
    sourceMap2801swap fusedMap2801swap sourceMap2801swap_checked fusedMap2801swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2801
#print axioms sourceMap2801swap_checked
#print axioms fusedMap2801swap_checked
#print axioms certified2801swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
