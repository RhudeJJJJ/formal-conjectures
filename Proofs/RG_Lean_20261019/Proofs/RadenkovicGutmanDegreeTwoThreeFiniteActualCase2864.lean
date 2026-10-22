/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2864 : Family 10 := level10.get ⟨1226,by decide⟩
def sourceMap2864 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2864 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2864_checked : acceptsGraphIso
    (source (graph core2864) (root 10) 0 4) DegreeTwoThreeSpectrum6427.graph sourceMap2864=true := by decide +kernel
theorem fusedMap2864_checked : acceptsGraphIso
    (fused (graph core2864) (root 10) 0 4) DegreeTwoThreeSpectrum6428.graph fusedMap2864=true := by decide +kernel
theorem certified2864 : Certified (graph core2864) (root 10) 0 4 :=
  of_native_maps core2864 DegreeTwoThreeSpectrum6427.graph DegreeTwoThreeSpectrum6428.graph
    sourceMap2864 fusedMap2864 sourceMap2864_checked fusedMap2864_checked
    DegreeTwoThreeFiniteComparisons.comparison2864
#print axioms sourceMap2864_checked
#print axioms fusedMap2864_checked
#print axioms certified2864
def sourceMap2864swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2864swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2864swap_checked : acceptsGraphIso
    (source (graph core2864) (root 10) 4 0) DegreeTwoThreeSpectrum6427.graph sourceMap2864swap=true := by decide +kernel
theorem fusedMap2864swap_checked : acceptsGraphIso
    (fused (graph core2864) (root 10) 4 0) DegreeTwoThreeSpectrum6428.graph fusedMap2864swap=true := by decide +kernel
theorem certified2864swap : Certified (graph core2864) (root 10) 4 0 :=
  of_native_maps core2864 DegreeTwoThreeSpectrum6427.graph DegreeTwoThreeSpectrum6428.graph
    sourceMap2864swap fusedMap2864swap sourceMap2864swap_checked fusedMap2864swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2864
#print axioms sourceMap2864swap_checked
#print axioms fusedMap2864swap_checked
#print axioms certified2864swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
