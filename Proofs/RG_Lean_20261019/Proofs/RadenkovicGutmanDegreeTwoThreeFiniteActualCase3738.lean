/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3738 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap3738 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (sourceLabel 3 0 10 v)
def fusedMap3738 : (Vertices 3 ⊕ Fin 12) → Fin 16 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 3 0 10 v)
theorem sourceMap3738_checked : acceptsGraphIso
    (source (graph core3738) (root 3) 0 10) DegreeTwoThreeSpectrum3863.graph sourceMap3738=true := by decide +kernel
theorem fusedMap3738_checked : acceptsGraphIso
    (fused (graph core3738) (root 3) 0 10) DegreeTwoThreeSpectrum3869.graph fusedMap3738=true := by decide +kernel
theorem certified3738 : Certified (graph core3738) (root 3) 0 10 :=
  of_native_maps core3738 DegreeTwoThreeSpectrum3863.graph DegreeTwoThreeSpectrum3869.graph
    sourceMap3738 fusedMap3738 sourceMap3738_checked fusedMap3738_checked
    DegreeTwoThreeFiniteComparisons.comparison3738
#print axioms sourceMap3738_checked
#print axioms fusedMap3738_checked
#print axioms certified3738
def sourceMap3738swap : (Vertices 3 ⊕ Fin 11 ⊕ Fin 1) → Fin 16 :=
  fun v => ![4,5,6,7,3,2,1,0,9,10,11,12,13,14,15,8] (sourceLabel 3 10 0 v)
def fusedMap3738swap : (Vertices 3 ⊕ Fin 12) → Fin 16 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 3 10 0 v)
theorem sourceMap3738swap_checked : acceptsGraphIso
    (source (graph core3738) (root 3) 10 0) DegreeTwoThreeSpectrum3863.graph sourceMap3738swap=true := by decide +kernel
theorem fusedMap3738swap_checked : acceptsGraphIso
    (fused (graph core3738) (root 3) 10 0) DegreeTwoThreeSpectrum3869.graph fusedMap3738swap=true := by decide +kernel
theorem certified3738swap : Certified (graph core3738) (root 3) 10 0 :=
  of_native_maps core3738 DegreeTwoThreeSpectrum3863.graph DegreeTwoThreeSpectrum3869.graph
    sourceMap3738swap fusedMap3738swap sourceMap3738swap_checked fusedMap3738swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3738
#print axioms sourceMap3738swap_checked
#print axioms fusedMap3738swap_checked
#print axioms certified3738swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
