/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3826 : Family 7 := level7.get ⟨104,by decide⟩
def sourceMap3826 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3826 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3826_checked : acceptsGraphIso
    (source (graph core3826) (root 7) 1 4) DegreeTwoThreeSpectrum3062.graph sourceMap3826=true := by decide +kernel
theorem fusedMap3826_checked : acceptsGraphIso
    (fused (graph core3826) (root 7) 1 4) DegreeTwoThreeSpectrum2455.graph fusedMap3826=true := by decide +kernel
theorem certified3826 : Certified (graph core3826) (root 7) 1 4 :=
  of_native_maps core3826 DegreeTwoThreeSpectrum3062.graph DegreeTwoThreeSpectrum2455.graph
    sourceMap3826 fusedMap3826 sourceMap3826_checked fusedMap3826_checked
    DegreeTwoThreeFiniteComparisons.comparison3826
#print axioms sourceMap3826_checked
#print axioms fusedMap3826_checked
#print axioms certified3826
def sourceMap3826swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,9,10] (sourceLabel 7 4 1 v)
def fusedMap3826swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3826swap_checked : acceptsGraphIso
    (source (graph core3826) (root 7) 4 1) DegreeTwoThreeSpectrum3062.graph sourceMap3826swap=true := by decide +kernel
theorem fusedMap3826swap_checked : acceptsGraphIso
    (fused (graph core3826) (root 7) 4 1) DegreeTwoThreeSpectrum2455.graph fusedMap3826swap=true := by decide +kernel
theorem certified3826swap : Certified (graph core3826) (root 7) 4 1 :=
  of_native_maps core3826 DegreeTwoThreeSpectrum3062.graph DegreeTwoThreeSpectrum2455.graph
    sourceMap3826swap fusedMap3826swap sourceMap3826swap_checked fusedMap3826swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3826
#print axioms sourceMap3826swap_checked
#print axioms fusedMap3826swap_checked
#print axioms certified3826swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
