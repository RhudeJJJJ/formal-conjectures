/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3146 : Family 8 := level8.get ⟨32,by decide⟩
def sourceMap3146 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12] (sourceLabel 8 0 5 v)
def fusedMap3146 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3146_checked : acceptsGraphIso
    (source (graph core3146) (root 8) 0 5) DegreeTwoThreeSpectrum4170.graph sourceMap3146=true := by decide +kernel
theorem fusedMap3146_checked : acceptsGraphIso
    (fused (graph core3146) (root 8) 0 5) DegreeTwoThreeSpectrum3888.graph fusedMap3146=true := by decide +kernel
theorem certified3146 : Certified (graph core3146) (root 8) 0 5 :=
  of_native_maps core3146 DegreeTwoThreeSpectrum4170.graph DegreeTwoThreeSpectrum3888.graph
    sourceMap3146 fusedMap3146 sourceMap3146_checked fusedMap3146_checked
    DegreeTwoThreeFiniteComparisons.comparison3146
#print axioms sourceMap3146_checked
#print axioms fusedMap3146_checked
#print axioms certified3146
def sourceMap3146swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,13,14,7,8,9,10,11,12,15] (sourceLabel 8 5 0 v)
def fusedMap3146swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3146swap_checked : acceptsGraphIso
    (source (graph core3146) (root 8) 5 0) DegreeTwoThreeSpectrum4170.graph sourceMap3146swap=true := by decide +kernel
theorem fusedMap3146swap_checked : acceptsGraphIso
    (fused (graph core3146) (root 8) 5 0) DegreeTwoThreeSpectrum3888.graph fusedMap3146swap=true := by decide +kernel
theorem certified3146swap : Certified (graph core3146) (root 8) 5 0 :=
  of_native_maps core3146 DegreeTwoThreeSpectrum4170.graph DegreeTwoThreeSpectrum3888.graph
    sourceMap3146swap fusedMap3146swap sourceMap3146swap_checked fusedMap3146swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3146
#print axioms sourceMap3146swap_checked
#print axioms fusedMap3146swap_checked
#print axioms certified3146swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
