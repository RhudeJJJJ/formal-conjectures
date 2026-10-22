/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3666 : Family 7 := level7.get ⟨23,by decide⟩
def sourceMap3666 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3666 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3666_checked : acceptsGraphIso
    (source (graph core3666) (root 7) 0 7) DegreeTwoThreeSpectrum5093.graph sourceMap3666=true := by decide +kernel
theorem fusedMap3666_checked : acceptsGraphIso
    (fused (graph core3666) (root 7) 0 7) DegreeTwoThreeSpectrum5096.graph fusedMap3666=true := by decide +kernel
theorem certified3666 : Certified (graph core3666) (root 7) 0 7 :=
  of_native_maps core3666 DegreeTwoThreeSpectrum5093.graph DegreeTwoThreeSpectrum5096.graph
    sourceMap3666 fusedMap3666 sourceMap3666_checked fusedMap3666_checked
    DegreeTwoThreeFiniteComparisons.comparison3666
#print axioms sourceMap3666_checked
#print axioms fusedMap3666_checked
#print axioms certified3666
def sourceMap3666swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,16,9] (sourceLabel 7 7 0 v)
def fusedMap3666swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3666swap_checked : acceptsGraphIso
    (source (graph core3666) (root 7) 7 0) DegreeTwoThreeSpectrum5093.graph sourceMap3666swap=true := by decide +kernel
theorem fusedMap3666swap_checked : acceptsGraphIso
    (fused (graph core3666) (root 7) 7 0) DegreeTwoThreeSpectrum5096.graph fusedMap3666swap=true := by decide +kernel
theorem certified3666swap : Certified (graph core3666) (root 7) 7 0 :=
  of_native_maps core3666 DegreeTwoThreeSpectrum5093.graph DegreeTwoThreeSpectrum5096.graph
    sourceMap3666swap fusedMap3666swap sourceMap3666swap_checked fusedMap3666swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3666
#print axioms sourceMap3666swap_checked
#print axioms fusedMap3666swap_checked
#print axioms certified3666swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
