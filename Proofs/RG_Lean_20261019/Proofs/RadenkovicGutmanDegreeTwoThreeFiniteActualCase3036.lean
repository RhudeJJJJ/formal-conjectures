/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3036 : Family 10 := level10.get ⟨1651,by decide⟩
def sourceMap3036 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3036 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3036_checked : acceptsGraphIso
    (source (graph core3036) (root 10) 0 4) DegreeTwoThreeSpectrum7211.graph sourceMap3036=true := by decide +kernel
theorem fusedMap3036_checked : acceptsGraphIso
    (fused (graph core3036) (root 10) 0 4) DegreeTwoThreeSpectrum6244.graph fusedMap3036=true := by decide +kernel
theorem certified3036 : Certified (graph core3036) (root 10) 0 4 :=
  of_native_maps core3036 DegreeTwoThreeSpectrum7211.graph DegreeTwoThreeSpectrum6244.graph
    sourceMap3036 fusedMap3036 sourceMap3036_checked fusedMap3036_checked
    DegreeTwoThreeFiniteComparisons.comparison3036
#print axioms sourceMap3036_checked
#print axioms fusedMap3036_checked
#print axioms certified3036
def sourceMap3036swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3036swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3036swap_checked : acceptsGraphIso
    (source (graph core3036) (root 10) 4 0) DegreeTwoThreeSpectrum7211.graph sourceMap3036swap=true := by decide +kernel
theorem fusedMap3036swap_checked : acceptsGraphIso
    (fused (graph core3036) (root 10) 4 0) DegreeTwoThreeSpectrum6244.graph fusedMap3036swap=true := by decide +kernel
theorem certified3036swap : Certified (graph core3036) (root 10) 4 0 :=
  of_native_maps core3036 DegreeTwoThreeSpectrum7211.graph DegreeTwoThreeSpectrum6244.graph
    sourceMap3036swap fusedMap3036swap sourceMap3036swap_checked fusedMap3036swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3036
#print axioms sourceMap3036swap_checked
#print axioms fusedMap3036swap_checked
#print axioms certified3036swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
