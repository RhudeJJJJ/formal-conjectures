/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3503 : Family 7 := level7.get ⟨11,by decide⟩
def sourceMap3503 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3503 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3503_checked : acceptsGraphIso
    (source (graph core3503) (root 7) 0 6) DegreeTwoThreeSpectrum3975.graph sourceMap3503=true := by decide +kernel
theorem fusedMap3503_checked : acceptsGraphIso
    (fused (graph core3503) (root 7) 0 6) DegreeTwoThreeSpectrum3858.graph fusedMap3503=true := by decide +kernel
theorem certified3503 : Certified (graph core3503) (root 7) 0 6 :=
  of_native_maps core3503 DegreeTwoThreeSpectrum3975.graph DegreeTwoThreeSpectrum3858.graph
    sourceMap3503 fusedMap3503 sourceMap3503_checked fusedMap3503_checked
    DegreeTwoThreeFiniteComparisons.comparison3503
#print axioms sourceMap3503_checked
#print axioms fusedMap3503_checked
#print axioms certified3503
def sourceMap3503swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3503swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3503swap_checked : acceptsGraphIso
    (source (graph core3503) (root 7) 6 0) DegreeTwoThreeSpectrum3975.graph sourceMap3503swap=true := by decide +kernel
theorem fusedMap3503swap_checked : acceptsGraphIso
    (fused (graph core3503) (root 7) 6 0) DegreeTwoThreeSpectrum3858.graph fusedMap3503swap=true := by decide +kernel
theorem certified3503swap : Certified (graph core3503) (root 7) 6 0 :=
  of_native_maps core3503 DegreeTwoThreeSpectrum3975.graph DegreeTwoThreeSpectrum3858.graph
    sourceMap3503swap fusedMap3503swap sourceMap3503swap_checked fusedMap3503swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3503
#print axioms sourceMap3503swap_checked
#print axioms fusedMap3503swap_checked
#print axioms certified3503swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
