/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2343 : Family 9 := level9.get ⟨406,by decide⟩
def sourceMap2343 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2343 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2343_checked : acceptsGraphIso
    (source (graph core2343) (root 9) 0 4) DegreeTwoThreeSpectrum4368.graph sourceMap2343=true := by decide +kernel
theorem fusedMap2343_checked : acceptsGraphIso
    (fused (graph core2343) (root 9) 0 4) DegreeTwoThreeSpectrum4369.graph fusedMap2343=true := by decide +kernel
theorem certified2343 : Certified (graph core2343) (root 9) 0 4 :=
  of_native_maps core2343 DegreeTwoThreeSpectrum4368.graph DegreeTwoThreeSpectrum4369.graph
    sourceMap2343 fusedMap2343 sourceMap2343_checked fusedMap2343_checked
    DegreeTwoThreeFiniteComparisons.comparison2343
#print axioms sourceMap2343_checked
#print axioms fusedMap2343_checked
#print axioms certified2343
def sourceMap2343swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2343swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2343swap_checked : acceptsGraphIso
    (source (graph core2343) (root 9) 4 0) DegreeTwoThreeSpectrum4368.graph sourceMap2343swap=true := by decide +kernel
theorem fusedMap2343swap_checked : acceptsGraphIso
    (fused (graph core2343) (root 9) 4 0) DegreeTwoThreeSpectrum4369.graph fusedMap2343swap=true := by decide +kernel
theorem certified2343swap : Certified (graph core2343) (root 9) 4 0 :=
  of_native_maps core2343 DegreeTwoThreeSpectrum4368.graph DegreeTwoThreeSpectrum4369.graph
    sourceMap2343swap fusedMap2343swap sourceMap2343swap_checked fusedMap2343swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2343
#print axioms sourceMap2343swap_checked
#print axioms fusedMap2343swap_checked
#print axioms certified2343swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
