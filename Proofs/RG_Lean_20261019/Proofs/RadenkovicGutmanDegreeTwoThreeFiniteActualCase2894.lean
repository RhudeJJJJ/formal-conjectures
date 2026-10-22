/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2894 : Family 10 := level10.get ⟨1308,by decide⟩
def sourceMap2894 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2894 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2894_checked : acceptsGraphIso
    (source (graph core2894) (root 10) 0 4) DegreeTwoThreeSpectrum6604.graph sourceMap2894=true := by decide +kernel
theorem fusedMap2894_checked : acceptsGraphIso
    (fused (graph core2894) (root 10) 0 4) DegreeTwoThreeSpectrum6605.graph fusedMap2894=true := by decide +kernel
theorem certified2894 : Certified (graph core2894) (root 10) 0 4 :=
  of_native_maps core2894 DegreeTwoThreeSpectrum6604.graph DegreeTwoThreeSpectrum6605.graph
    sourceMap2894 fusedMap2894 sourceMap2894_checked fusedMap2894_checked
    DegreeTwoThreeFiniteComparisons.comparison2894
#print axioms sourceMap2894_checked
#print axioms fusedMap2894_checked
#print axioms certified2894
def sourceMap2894swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2894swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2894swap_checked : acceptsGraphIso
    (source (graph core2894) (root 10) 4 0) DegreeTwoThreeSpectrum6604.graph sourceMap2894swap=true := by decide +kernel
theorem fusedMap2894swap_checked : acceptsGraphIso
    (fused (graph core2894) (root 10) 4 0) DegreeTwoThreeSpectrum6605.graph fusedMap2894swap=true := by decide +kernel
theorem certified2894swap : Certified (graph core2894) (root 10) 4 0 :=
  of_native_maps core2894 DegreeTwoThreeSpectrum6604.graph DegreeTwoThreeSpectrum6605.graph
    sourceMap2894swap fusedMap2894swap sourceMap2894swap_checked fusedMap2894swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2894
#print axioms sourceMap2894swap_checked
#print axioms fusedMap2894swap_checked
#print axioms certified2894swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
