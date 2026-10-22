/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3429 : Family 9 := level9.get ⟨566,by decide⟩
def sourceMap3429 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3429 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3429_checked : acceptsGraphIso
    (source (graph core3429) (root 9) 0 5) DegreeTwoThreeSpectrum6058.graph sourceMap3429=true := by decide +kernel
theorem fusedMap3429_checked : acceptsGraphIso
    (fused (graph core3429) (root 9) 0 5) DegreeTwoThreeSpectrum6059.graph fusedMap3429=true := by decide +kernel
theorem certified3429 : Certified (graph core3429) (root 9) 0 5 :=
  of_native_maps core3429 DegreeTwoThreeSpectrum6058.graph DegreeTwoThreeSpectrum6059.graph
    sourceMap3429 fusedMap3429 sourceMap3429_checked fusedMap3429_checked
    DegreeTwoThreeFiniteComparisons.comparison3429
#print axioms sourceMap3429_checked
#print axioms fusedMap3429_checked
#print axioms certified3429
def sourceMap3429swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3429swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3429swap_checked : acceptsGraphIso
    (source (graph core3429) (root 9) 5 0) DegreeTwoThreeSpectrum6058.graph sourceMap3429swap=true := by decide +kernel
theorem fusedMap3429swap_checked : acceptsGraphIso
    (fused (graph core3429) (root 9) 5 0) DegreeTwoThreeSpectrum6059.graph fusedMap3429swap=true := by decide +kernel
theorem certified3429swap : Certified (graph core3429) (root 9) 5 0 :=
  of_native_maps core3429 DegreeTwoThreeSpectrum6058.graph DegreeTwoThreeSpectrum6059.graph
    sourceMap3429swap fusedMap3429swap sourceMap3429swap_checked fusedMap3429swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3429
#print axioms sourceMap3429swap_checked
#print axioms fusedMap3429swap_checked
#print axioms certified3429swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
