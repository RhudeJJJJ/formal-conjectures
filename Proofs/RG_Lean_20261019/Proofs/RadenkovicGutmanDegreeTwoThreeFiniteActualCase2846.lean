/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2846 : Family 10 := level10.get ⟨1192,by decide⟩
def sourceMap2846 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2846 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2846_checked : acceptsGraphIso
    (source (graph core2846) (root 10) 0 4) DegreeTwoThreeSpectrum6364.graph sourceMap2846=true := by decide +kernel
theorem fusedMap2846_checked : acceptsGraphIso
    (fused (graph core2846) (root 10) 0 4) DegreeTwoThreeSpectrum6365.graph fusedMap2846=true := by decide +kernel
theorem certified2846 : Certified (graph core2846) (root 10) 0 4 :=
  of_native_maps core2846 DegreeTwoThreeSpectrum6364.graph DegreeTwoThreeSpectrum6365.graph
    sourceMap2846 fusedMap2846 sourceMap2846_checked fusedMap2846_checked
    DegreeTwoThreeFiniteComparisons.comparison2846
#print axioms sourceMap2846_checked
#print axioms fusedMap2846_checked
#print axioms certified2846
def sourceMap2846swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2846swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2846swap_checked : acceptsGraphIso
    (source (graph core2846) (root 10) 4 0) DegreeTwoThreeSpectrum6364.graph sourceMap2846swap=true := by decide +kernel
theorem fusedMap2846swap_checked : acceptsGraphIso
    (fused (graph core2846) (root 10) 4 0) DegreeTwoThreeSpectrum6365.graph fusedMap2846swap=true := by decide +kernel
theorem certified2846swap : Certified (graph core2846) (root 10) 4 0 :=
  of_native_maps core2846 DegreeTwoThreeSpectrum6364.graph DegreeTwoThreeSpectrum6365.graph
    sourceMap2846swap fusedMap2846swap sourceMap2846swap_checked fusedMap2846swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2846
#print axioms sourceMap2846swap_checked
#print axioms fusedMap2846swap_checked
#print axioms certified2846swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
