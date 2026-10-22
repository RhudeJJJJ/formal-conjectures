/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3834 : Family 8 := level8.get ⟨38,by decide⟩
def sourceMap3834 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,13,14,8,9,10,11,12] (sourceLabel 8 1 4 v)
def fusedMap3834 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3834_checked : acceptsGraphIso
    (source (graph core3834) (root 8) 1 4) DegreeTwoThreeSpectrum4258.graph sourceMap3834=true := by decide +kernel
theorem fusedMap3834_checked : acceptsGraphIso
    (fused (graph core3834) (root 8) 1 4) DegreeTwoThreeSpectrum3914.graph fusedMap3834=true := by decide +kernel
theorem certified3834 : Certified (graph core3834) (root 8) 1 4 :=
  of_native_maps core3834 DegreeTwoThreeSpectrum4258.graph DegreeTwoThreeSpectrum3914.graph
    sourceMap3834 fusedMap3834 sourceMap3834_checked fusedMap3834_checked
    DegreeTwoThreeFiniteComparisons.comparison3834
#print axioms sourceMap3834_checked
#print axioms fusedMap3834_checked
#print axioms certified3834
def sourceMap3834swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,15,8,9,10,11,12,13,14] (sourceLabel 8 4 1 v)
def fusedMap3834swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3834swap_checked : acceptsGraphIso
    (source (graph core3834) (root 8) 4 1) DegreeTwoThreeSpectrum4258.graph sourceMap3834swap=true := by decide +kernel
theorem fusedMap3834swap_checked : acceptsGraphIso
    (fused (graph core3834) (root 8) 4 1) DegreeTwoThreeSpectrum3914.graph fusedMap3834swap=true := by decide +kernel
theorem certified3834swap : Certified (graph core3834) (root 8) 4 1 :=
  of_native_maps core3834 DegreeTwoThreeSpectrum4258.graph DegreeTwoThreeSpectrum3914.graph
    sourceMap3834swap fusedMap3834swap sourceMap3834swap_checked fusedMap3834swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3834
#print axioms sourceMap3834swap_checked
#print axioms fusedMap3834swap_checked
#print axioms certified3834swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
