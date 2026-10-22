/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3170 : Family 8 := level8.get ⟨111,by decide⟩
def sourceMap3170 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3170 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3170_checked : acceptsGraphIso
    (source (graph core3170) (root 8) 0 5) DegreeTwoThreeSpectrum4284.graph sourceMap3170=true := by decide +kernel
theorem fusedMap3170_checked : acceptsGraphIso
    (fused (graph core3170) (root 8) 0 5) DegreeTwoThreeSpectrum3920.graph fusedMap3170=true := by decide +kernel
theorem certified3170 : Certified (graph core3170) (root 8) 0 5 :=
  of_native_maps core3170 DegreeTwoThreeSpectrum4284.graph DegreeTwoThreeSpectrum3920.graph
    sourceMap3170 fusedMap3170 sourceMap3170_checked fusedMap3170_checked
    DegreeTwoThreeFiniteComparisons.comparison3170
#print axioms sourceMap3170_checked
#print axioms fusedMap3170_checked
#print axioms certified3170
def sourceMap3170swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3170swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3170swap_checked : acceptsGraphIso
    (source (graph core3170) (root 8) 5 0) DegreeTwoThreeSpectrum4284.graph sourceMap3170swap=true := by decide +kernel
theorem fusedMap3170swap_checked : acceptsGraphIso
    (fused (graph core3170) (root 8) 5 0) DegreeTwoThreeSpectrum3920.graph fusedMap3170swap=true := by decide +kernel
theorem certified3170swap : Certified (graph core3170) (root 8) 5 0 :=
  of_native_maps core3170 DegreeTwoThreeSpectrum4284.graph DegreeTwoThreeSpectrum3920.graph
    sourceMap3170swap fusedMap3170swap sourceMap3170swap_checked fusedMap3170swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3170
#print axioms sourceMap3170swap_checked
#print axioms fusedMap3170swap_checked
#print axioms certified3170swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
