/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3883 : Family 8 := level8.get ⟨175,by decide⟩
def sourceMap3883 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3883 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3883_checked : acceptsGraphIso
    (source (graph core3883) (root 8) 1 4) DegreeTwoThreeSpectrum4613.graph sourceMap3883=true := by decide +kernel
theorem fusedMap3883_checked : acceptsGraphIso
    (fused (graph core3883) (root 8) 1 4) DegreeTwoThreeSpectrum4092.graph fusedMap3883=true := by decide +kernel
theorem certified3883 : Certified (graph core3883) (root 8) 1 4 :=
  of_native_maps core3883 DegreeTwoThreeSpectrum4613.graph DegreeTwoThreeSpectrum4092.graph
    sourceMap3883 fusedMap3883 sourceMap3883_checked fusedMap3883_checked
    DegreeTwoThreeFiniteComparisons.comparison3883
#print axioms sourceMap3883_checked
#print axioms fusedMap3883_checked
#print axioms certified3883
def sourceMap3883swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3883swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3883swap_checked : acceptsGraphIso
    (source (graph core3883) (root 8) 4 1) DegreeTwoThreeSpectrum4613.graph sourceMap3883swap=true := by decide +kernel
theorem fusedMap3883swap_checked : acceptsGraphIso
    (fused (graph core3883) (root 8) 4 1) DegreeTwoThreeSpectrum4092.graph fusedMap3883swap=true := by decide +kernel
theorem certified3883swap : Certified (graph core3883) (root 8) 4 1 :=
  of_native_maps core3883 DegreeTwoThreeSpectrum4613.graph DegreeTwoThreeSpectrum4092.graph
    sourceMap3883swap fusedMap3883swap sourceMap3883swap_checked fusedMap3883swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3883
#print axioms sourceMap3883swap_checked
#print axioms fusedMap3883swap_checked
#print axioms certified3883swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
