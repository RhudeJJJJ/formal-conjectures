/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2787 : Family 10 := level10.get ⟨1043,by decide⟩
def sourceMap2787 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2787 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2787_checked : acceptsGraphIso
    (source (graph core2787) (root 10) 0 4) DegreeTwoThreeSpectrum6069.graph sourceMap2787=true := by decide +kernel
theorem fusedMap2787_checked : acceptsGraphIso
    (fused (graph core2787) (root 10) 0 4) DegreeTwoThreeSpectrum6070.graph fusedMap2787=true := by decide +kernel
theorem certified2787 : Certified (graph core2787) (root 10) 0 4 :=
  of_native_maps core2787 DegreeTwoThreeSpectrum6069.graph DegreeTwoThreeSpectrum6070.graph
    sourceMap2787 fusedMap2787 sourceMap2787_checked fusedMap2787_checked
    DegreeTwoThreeFiniteComparisons.comparison2787
#print axioms sourceMap2787_checked
#print axioms fusedMap2787_checked
#print axioms certified2787
def sourceMap2787swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2787swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2787swap_checked : acceptsGraphIso
    (source (graph core2787) (root 10) 4 0) DegreeTwoThreeSpectrum6069.graph sourceMap2787swap=true := by decide +kernel
theorem fusedMap2787swap_checked : acceptsGraphIso
    (fused (graph core2787) (root 10) 4 0) DegreeTwoThreeSpectrum6070.graph fusedMap2787swap=true := by decide +kernel
theorem certified2787swap : Certified (graph core2787) (root 10) 4 0 :=
  of_native_maps core2787 DegreeTwoThreeSpectrum6069.graph DegreeTwoThreeSpectrum6070.graph
    sourceMap2787swap fusedMap2787swap sourceMap2787swap_checked fusedMap2787swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2787
#print axioms sourceMap2787swap_checked
#print axioms fusedMap2787swap_checked
#print axioms certified2787swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
