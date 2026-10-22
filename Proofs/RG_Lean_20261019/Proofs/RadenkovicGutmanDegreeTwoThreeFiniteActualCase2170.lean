/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2170 : Family 8 := level8.get ⟨165,by decide⟩
def sourceMap2170 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2170 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2170_checked : acceptsGraphIso
    (source (graph core2170) (root 8) 0 4) DegreeTwoThreeSpectrum2835.graph sourceMap2170=true := by decide +kernel
theorem fusedMap2170_checked : acceptsGraphIso
    (fused (graph core2170) (root 8) 0 4) DegreeTwoThreeSpectrum2837.graph fusedMap2170=true := by decide +kernel
theorem certified2170 : Certified (graph core2170) (root 8) 0 4 :=
  of_native_maps core2170 DegreeTwoThreeSpectrum2835.graph DegreeTwoThreeSpectrum2837.graph
    sourceMap2170 fusedMap2170 sourceMap2170_checked fusedMap2170_checked
    DegreeTwoThreeFiniteComparisons.comparison2170
#print axioms sourceMap2170_checked
#print axioms fusedMap2170_checked
#print axioms certified2170
def sourceMap2170swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2170swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2170swap_checked : acceptsGraphIso
    (source (graph core2170) (root 8) 4 0) DegreeTwoThreeSpectrum2835.graph sourceMap2170swap=true := by decide +kernel
theorem fusedMap2170swap_checked : acceptsGraphIso
    (fused (graph core2170) (root 8) 4 0) DegreeTwoThreeSpectrum2837.graph fusedMap2170swap=true := by decide +kernel
theorem certified2170swap : Certified (graph core2170) (root 8) 4 0 :=
  of_native_maps core2170 DegreeTwoThreeSpectrum2835.graph DegreeTwoThreeSpectrum2837.graph
    sourceMap2170swap fusedMap2170swap sourceMap2170swap_checked fusedMap2170swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2170
#print axioms sourceMap2170swap_checked
#print axioms fusedMap2170swap_checked
#print axioms certified2170swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
