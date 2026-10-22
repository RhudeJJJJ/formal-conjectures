/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2378 : Family 9 := level9.get ⟨493,by decide⟩
def sourceMap2378 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2378 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2378_checked : acceptsGraphIso
    (source (graph core2378) (root 9) 0 4) DegreeTwoThreeSpectrum4567.graph sourceMap2378=true := by decide +kernel
theorem fusedMap2378_checked : acceptsGraphIso
    (fused (graph core2378) (root 9) 0 4) DegreeTwoThreeSpectrum4568.graph fusedMap2378=true := by decide +kernel
theorem certified2378 : Certified (graph core2378) (root 9) 0 4 :=
  of_native_maps core2378 DegreeTwoThreeSpectrum4567.graph DegreeTwoThreeSpectrum4568.graph
    sourceMap2378 fusedMap2378 sourceMap2378_checked fusedMap2378_checked
    DegreeTwoThreeFiniteComparisons.comparison2378
#print axioms sourceMap2378_checked
#print axioms fusedMap2378_checked
#print axioms certified2378
def sourceMap2378swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2378swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2378swap_checked : acceptsGraphIso
    (source (graph core2378) (root 9) 4 0) DegreeTwoThreeSpectrum4567.graph sourceMap2378swap=true := by decide +kernel
theorem fusedMap2378swap_checked : acceptsGraphIso
    (fused (graph core2378) (root 9) 4 0) DegreeTwoThreeSpectrum4568.graph fusedMap2378swap=true := by decide +kernel
theorem certified2378swap : Certified (graph core2378) (root 9) 4 0 :=
  of_native_maps core2378 DegreeTwoThreeSpectrum4567.graph DegreeTwoThreeSpectrum4568.graph
    sourceMap2378swap fusedMap2378swap sourceMap2378swap_checked fusedMap2378swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2378
#print axioms sourceMap2378swap_checked
#print axioms fusedMap2378swap_checked
#print axioms certified2378swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
