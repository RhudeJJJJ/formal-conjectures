/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons53
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2695 : Family 10 := level10.get ⟨810,by decide⟩
def sourceMap2695 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2695 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2695_checked : acceptsGraphIso
    (source (graph core2695) (root 10) 0 4) DegreeTwoThreeSpectrum6770.graph sourceMap2695=true := by decide +kernel
theorem fusedMap2695_checked : acceptsGraphIso
    (fused (graph core2695) (root 10) 0 4) DegreeTwoThreeSpectrum5606.graph fusedMap2695=true := by decide +kernel
theorem certified2695 : Certified (graph core2695) (root 10) 0 4 :=
  of_native_maps core2695 DegreeTwoThreeSpectrum6770.graph DegreeTwoThreeSpectrum5606.graph
    sourceMap2695 fusedMap2695 sourceMap2695_checked fusedMap2695_checked
    DegreeTwoThreeFiniteComparisons.comparison2695
#print axioms sourceMap2695_checked
#print axioms fusedMap2695_checked
#print axioms certified2695
def sourceMap2695swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2695swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2695swap_checked : acceptsGraphIso
    (source (graph core2695) (root 10) 4 0) DegreeTwoThreeSpectrum6770.graph sourceMap2695swap=true := by decide +kernel
theorem fusedMap2695swap_checked : acceptsGraphIso
    (fused (graph core2695) (root 10) 4 0) DegreeTwoThreeSpectrum5606.graph fusedMap2695swap=true := by decide +kernel
theorem certified2695swap : Certified (graph core2695) (root 10) 4 0 :=
  of_native_maps core2695 DegreeTwoThreeSpectrum6770.graph DegreeTwoThreeSpectrum5606.graph
    sourceMap2695swap fusedMap2695swap sourceMap2695swap_checked fusedMap2695swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2695
#print axioms sourceMap2695swap_checked
#print axioms fusedMap2695swap_checked
#print axioms certified2695swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
