/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2697 : Family 10 := level10.get ⟨814,by decide⟩
def sourceMap2697 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2697 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2697_checked : acceptsGraphIso
    (source (graph core2697) (root 10) 0 4) DegreeTwoThreeSpectrum6773.graph sourceMap2697=true := by decide +kernel
theorem fusedMap2697_checked : acceptsGraphIso
    (fused (graph core2697) (root 10) 0 4) DegreeTwoThreeSpectrum5613.graph fusedMap2697=true := by decide +kernel
theorem certified2697 : Certified (graph core2697) (root 10) 0 4 :=
  of_native_maps core2697 DegreeTwoThreeSpectrum6773.graph DegreeTwoThreeSpectrum5613.graph
    sourceMap2697 fusedMap2697 sourceMap2697_checked fusedMap2697_checked
    DegreeTwoThreeFiniteComparisons.comparison2697
#print axioms sourceMap2697_checked
#print axioms fusedMap2697_checked
#print axioms certified2697
def sourceMap2697swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2697swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2697swap_checked : acceptsGraphIso
    (source (graph core2697) (root 10) 4 0) DegreeTwoThreeSpectrum6773.graph sourceMap2697swap=true := by decide +kernel
theorem fusedMap2697swap_checked : acceptsGraphIso
    (fused (graph core2697) (root 10) 4 0) DegreeTwoThreeSpectrum5613.graph fusedMap2697swap=true := by decide +kernel
theorem certified2697swap : Certified (graph core2697) (root 10) 4 0 :=
  of_native_maps core2697 DegreeTwoThreeSpectrum6773.graph DegreeTwoThreeSpectrum5613.graph
    sourceMap2697swap fusedMap2697swap sourceMap2697swap_checked fusedMap2697swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2697
#print axioms sourceMap2697swap_checked
#print axioms fusedMap2697swap_checked
#print axioms certified2697swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
