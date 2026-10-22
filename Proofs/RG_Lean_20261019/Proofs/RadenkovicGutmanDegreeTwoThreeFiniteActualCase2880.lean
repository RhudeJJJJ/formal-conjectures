/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2880 : Family 10 := level10.get ⟨1274,by decide⟩
def sourceMap2880 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2880 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2880_checked : acceptsGraphIso
    (source (graph core2880) (root 10) 0 4) DegreeTwoThreeSpectrum6538.graph sourceMap2880=true := by decide +kernel
theorem fusedMap2880_checked : acceptsGraphIso
    (fused (graph core2880) (root 10) 0 4) DegreeTwoThreeSpectrum6539.graph fusedMap2880=true := by decide +kernel
theorem certified2880 : Certified (graph core2880) (root 10) 0 4 :=
  of_native_maps core2880 DegreeTwoThreeSpectrum6538.graph DegreeTwoThreeSpectrum6539.graph
    sourceMap2880 fusedMap2880 sourceMap2880_checked fusedMap2880_checked
    DegreeTwoThreeFiniteComparisons.comparison2880
#print axioms sourceMap2880_checked
#print axioms fusedMap2880_checked
#print axioms certified2880
def sourceMap2880swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2880swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2880swap_checked : acceptsGraphIso
    (source (graph core2880) (root 10) 4 0) DegreeTwoThreeSpectrum6538.graph sourceMap2880swap=true := by decide +kernel
theorem fusedMap2880swap_checked : acceptsGraphIso
    (fused (graph core2880) (root 10) 4 0) DegreeTwoThreeSpectrum6539.graph fusedMap2880swap=true := by decide +kernel
theorem certified2880swap : Certified (graph core2880) (root 10) 4 0 :=
  of_native_maps core2880 DegreeTwoThreeSpectrum6538.graph DegreeTwoThreeSpectrum6539.graph
    sourceMap2880swap fusedMap2880swap sourceMap2880swap_checked fusedMap2880swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2880
#print axioms sourceMap2880swap_checked
#print axioms fusedMap2880swap_checked
#print axioms certified2880swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
