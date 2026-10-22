/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2399 : Family 9 := level9.get ⟨544,by decide⟩
def sourceMap2399 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2399 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2399_checked : acceptsGraphIso
    (source (graph core2399) (root 9) 0 4) DegreeTwoThreeSpectrum4669.graph sourceMap2399=true := by decide +kernel
theorem fusedMap2399_checked : acceptsGraphIso
    (fused (graph core2399) (root 9) 0 4) DegreeTwoThreeSpectrum4172.graph fusedMap2399=true := by decide +kernel
theorem certified2399 : Certified (graph core2399) (root 9) 0 4 :=
  of_native_maps core2399 DegreeTwoThreeSpectrum4669.graph DegreeTwoThreeSpectrum4172.graph
    sourceMap2399 fusedMap2399 sourceMap2399_checked fusedMap2399_checked
    DegreeTwoThreeFiniteComparisons.comparison2399
#print axioms sourceMap2399_checked
#print axioms fusedMap2399_checked
#print axioms certified2399
def sourceMap2399swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,11] (sourceLabel 9 4 0 v)
def fusedMap2399swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2399swap_checked : acceptsGraphIso
    (source (graph core2399) (root 9) 4 0) DegreeTwoThreeSpectrum4669.graph sourceMap2399swap=true := by decide +kernel
theorem fusedMap2399swap_checked : acceptsGraphIso
    (fused (graph core2399) (root 9) 4 0) DegreeTwoThreeSpectrum4172.graph fusedMap2399swap=true := by decide +kernel
theorem certified2399swap : Certified (graph core2399) (root 9) 4 0 :=
  of_native_maps core2399 DegreeTwoThreeSpectrum4669.graph DegreeTwoThreeSpectrum4172.graph
    sourceMap2399swap fusedMap2399swap sourceMap2399swap_checked fusedMap2399swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2399
#print axioms sourceMap2399swap_checked
#print axioms fusedMap2399swap_checked
#print axioms certified2399swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
