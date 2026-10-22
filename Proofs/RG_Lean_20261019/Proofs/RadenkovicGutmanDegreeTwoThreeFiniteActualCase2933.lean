/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2933 : Family 10 := level10.get ⟨1391,by decide⟩
def sourceMap2933 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2933 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2933_checked : acceptsGraphIso
    (source (graph core2933) (root 10) 0 4) DegreeTwoThreeSpectrum6754.graph sourceMap2933=true := by decide +kernel
theorem fusedMap2933_checked : acceptsGraphIso
    (fused (graph core2933) (root 10) 0 4) DegreeTwoThreeSpectrum6755.graph fusedMap2933=true := by decide +kernel
theorem certified2933 : Certified (graph core2933) (root 10) 0 4 :=
  of_native_maps core2933 DegreeTwoThreeSpectrum6754.graph DegreeTwoThreeSpectrum6755.graph
    sourceMap2933 fusedMap2933 sourceMap2933_checked fusedMap2933_checked
    DegreeTwoThreeFiniteComparisons.comparison2933
#print axioms sourceMap2933_checked
#print axioms fusedMap2933_checked
#print axioms certified2933
def sourceMap2933swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2933swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2933swap_checked : acceptsGraphIso
    (source (graph core2933) (root 10) 4 0) DegreeTwoThreeSpectrum6754.graph sourceMap2933swap=true := by decide +kernel
theorem fusedMap2933swap_checked : acceptsGraphIso
    (fused (graph core2933) (root 10) 4 0) DegreeTwoThreeSpectrum6755.graph fusedMap2933swap=true := by decide +kernel
theorem certified2933swap : Certified (graph core2933) (root 10) 4 0 :=
  of_native_maps core2933 DegreeTwoThreeSpectrum6754.graph DegreeTwoThreeSpectrum6755.graph
    sourceMap2933swap fusedMap2933swap sourceMap2933swap_checked fusedMap2933swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2933
#print axioms sourceMap2933swap_checked
#print axioms fusedMap2933swap_checked
#print axioms certified2933swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
