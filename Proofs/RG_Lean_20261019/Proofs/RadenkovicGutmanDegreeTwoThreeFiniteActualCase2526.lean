/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2526 : Family 10 := level10.get ⟨301,by decide⟩
def sourceMap2526 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2526 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2526_checked : acceptsGraphIso
    (source (graph core2526) (root 10) 0 4) DegreeTwoThreeSpectrum5476.graph sourceMap2526=true := by decide +kernel
theorem fusedMap2526_checked : acceptsGraphIso
    (fused (graph core2526) (root 10) 0 4) DegreeTwoThreeSpectrum5477.graph fusedMap2526=true := by decide +kernel
theorem certified2526 : Certified (graph core2526) (root 10) 0 4 :=
  of_native_maps core2526 DegreeTwoThreeSpectrum5476.graph DegreeTwoThreeSpectrum5477.graph
    sourceMap2526 fusedMap2526 sourceMap2526_checked fusedMap2526_checked
    DegreeTwoThreeFiniteComparisons.comparison2526
#print axioms sourceMap2526_checked
#print axioms fusedMap2526_checked
#print axioms certified2526
def sourceMap2526swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2526swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2526swap_checked : acceptsGraphIso
    (source (graph core2526) (root 10) 4 0) DegreeTwoThreeSpectrum5476.graph sourceMap2526swap=true := by decide +kernel
theorem fusedMap2526swap_checked : acceptsGraphIso
    (fused (graph core2526) (root 10) 4 0) DegreeTwoThreeSpectrum5477.graph fusedMap2526swap=true := by decide +kernel
theorem certified2526swap : Certified (graph core2526) (root 10) 4 0 :=
  of_native_maps core2526 DegreeTwoThreeSpectrum5476.graph DegreeTwoThreeSpectrum5477.graph
    sourceMap2526swap fusedMap2526swap sourceMap2526swap_checked fusedMap2526swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2526
#print axioms sourceMap2526swap_checked
#print axioms fusedMap2526swap_checked
#print axioms certified2526swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
