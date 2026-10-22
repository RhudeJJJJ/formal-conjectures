/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2641 : Family 10 := level10.get ⟨657,by decide⟩
def sourceMap2641 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2641 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2641_checked : acceptsGraphIso
    (source (graph core2641) (root 10) 0 4) DegreeTwoThreeSpectrum6438.graph sourceMap2641=true := by decide +kernel
theorem fusedMap2641_checked : acceptsGraphIso
    (fused (graph core2641) (root 10) 0 4) DegreeTwoThreeSpectrum5366.graph fusedMap2641=true := by decide +kernel
theorem certified2641 : Certified (graph core2641) (root 10) 0 4 :=
  of_native_maps core2641 DegreeTwoThreeSpectrum6438.graph DegreeTwoThreeSpectrum5366.graph
    sourceMap2641 fusedMap2641 sourceMap2641_checked fusedMap2641_checked
    DegreeTwoThreeFiniteComparisons.comparison2641
#print axioms sourceMap2641_checked
#print axioms fusedMap2641_checked
#print axioms certified2641
def sourceMap2641swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2641swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2641swap_checked : acceptsGraphIso
    (source (graph core2641) (root 10) 4 0) DegreeTwoThreeSpectrum6438.graph sourceMap2641swap=true := by decide +kernel
theorem fusedMap2641swap_checked : acceptsGraphIso
    (fused (graph core2641) (root 10) 4 0) DegreeTwoThreeSpectrum5366.graph fusedMap2641swap=true := by decide +kernel
theorem certified2641swap : Certified (graph core2641) (root 10) 4 0 :=
  of_native_maps core2641 DegreeTwoThreeSpectrum6438.graph DegreeTwoThreeSpectrum5366.graph
    sourceMap2641swap fusedMap2641swap sourceMap2641swap_checked fusedMap2641swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2641
#print axioms sourceMap2641swap_checked
#print axioms fusedMap2641swap_checked
#print axioms certified2641swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
