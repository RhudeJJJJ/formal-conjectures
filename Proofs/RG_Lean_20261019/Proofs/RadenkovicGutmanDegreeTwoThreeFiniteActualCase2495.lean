/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2495 : Family 10 := level10.get ⟨185,by decide⟩
def sourceMap2495 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,7,8,9,10,2,3,4,5,6] (sourceLabel 10 0 4 v)
def fusedMap2495 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,7,8,9,1,2,3,4,5,6] (fusedLabel 10 0 4 v)
theorem sourceMap2495_checked : acceptsGraphIso
    (source (graph core2495) (root 10) 0 4) DegreeTwoThreeSpectrum5925.graph sourceMap2495=true := by decide +kernel
theorem fusedMap2495_checked : acceptsGraphIso
    (fused (graph core2495) (root 10) 0 4) DegreeTwoThreeSpectrum5124.graph fusedMap2495=true := by decide +kernel
theorem certified2495 : Certified (graph core2495) (root 10) 0 4 :=
  of_native_maps core2495 DegreeTwoThreeSpectrum5925.graph DegreeTwoThreeSpectrum5124.graph
    sourceMap2495 fusedMap2495 sourceMap2495_checked fusedMap2495_checked
    DegreeTwoThreeFiniteComparisons.comparison2495
#print axioms sourceMap2495_checked
#print axioms fusedMap2495_checked
#print axioms certified2495
def sourceMap2495swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,7,8,9,2,3,4,5,6,10] (sourceLabel 10 4 0 v)
def fusedMap2495swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,7,8,9,1,2,3,4,5,6] (fusedLabel 10 4 0 v)
theorem sourceMap2495swap_checked : acceptsGraphIso
    (source (graph core2495) (root 10) 4 0) DegreeTwoThreeSpectrum5925.graph sourceMap2495swap=true := by decide +kernel
theorem fusedMap2495swap_checked : acceptsGraphIso
    (fused (graph core2495) (root 10) 4 0) DegreeTwoThreeSpectrum5124.graph fusedMap2495swap=true := by decide +kernel
theorem certified2495swap : Certified (graph core2495) (root 10) 4 0 :=
  of_native_maps core2495 DegreeTwoThreeSpectrum5925.graph DegreeTwoThreeSpectrum5124.graph
    sourceMap2495swap fusedMap2495swap sourceMap2495swap_checked fusedMap2495swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2495
#print axioms sourceMap2495swap_checked
#print axioms fusedMap2495swap_checked
#print axioms certified2495swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
