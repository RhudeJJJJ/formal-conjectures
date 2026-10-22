/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3907 : Family 8 := level8.get ⟨231,by decide⟩
def sourceMap3907 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,9,10,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3907 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3907_checked : acceptsGraphIso
    (source (graph core3907) (root 8) 1 4) DegreeTwoThreeSpectrum4790.graph sourceMap3907=true := by decide +kernel
theorem fusedMap3907_checked : acceptsGraphIso
    (fused (graph core3907) (root 8) 1 4) DegreeTwoThreeSpectrum4394.graph fusedMap3907=true := by decide +kernel
theorem certified3907 : Certified (graph core3907) (root 8) 1 4 :=
  of_native_maps core3907 DegreeTwoThreeSpectrum4790.graph DegreeTwoThreeSpectrum4394.graph
    sourceMap3907 fusedMap3907 sourceMap3907_checked fusedMap3907_checked
    DegreeTwoThreeFiniteComparisons.comparison3907
#print axioms sourceMap3907_checked
#print axioms fusedMap3907_checked
#print axioms certified3907
def sourceMap3907swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,0,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3907swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3907swap_checked : acceptsGraphIso
    (source (graph core3907) (root 8) 4 1) DegreeTwoThreeSpectrum4790.graph sourceMap3907swap=true := by decide +kernel
theorem fusedMap3907swap_checked : acceptsGraphIso
    (fused (graph core3907) (root 8) 4 1) DegreeTwoThreeSpectrum4394.graph fusedMap3907swap=true := by decide +kernel
theorem certified3907swap : Certified (graph core3907) (root 8) 4 1 :=
  of_native_maps core3907 DegreeTwoThreeSpectrum4790.graph DegreeTwoThreeSpectrum4394.graph
    sourceMap3907swap fusedMap3907swap sourceMap3907swap_checked fusedMap3907swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3907
#print axioms sourceMap3907swap_checked
#print axioms fusedMap3907swap_checked
#print axioms certified3907swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
