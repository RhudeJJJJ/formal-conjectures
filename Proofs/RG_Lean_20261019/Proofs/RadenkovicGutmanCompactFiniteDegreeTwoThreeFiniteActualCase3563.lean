/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3563 : Family 8 := level8.get ⟨91,by decide⟩
def sourceMap3563 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3563 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3563_checked : acceptsGraphIso
    (source (graph core3563) (root 8) 0 6) DegreeTwoThreeSpectrum5925.graph sourceMap3563=true := by decide +kernel
theorem fusedMap3563_checked : acceptsGraphIso
    (fused (graph core3563) (root 8) 0 6) DegreeTwoThreeSpectrum5106.graph fusedMap3563=true := by decide +kernel
theorem certified3563 : Certified (graph core3563) (root 8) 0 6 :=
  of_native_maps core3563 DegreeTwoThreeSpectrum5925.graph DegreeTwoThreeSpectrum5106.graph
    sourceMap3563 fusedMap3563 sourceMap3563_checked fusedMap3563_checked
    DegreeTwoThreeFiniteComparisons.comparison3563
#print axioms sourceMap3563_checked
#print axioms fusedMap3563_checked
#print axioms certified3563
def sourceMap3563swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3563swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3563swap_checked : acceptsGraphIso
    (source (graph core3563) (root 8) 6 0) DegreeTwoThreeSpectrum5925.graph sourceMap3563swap=true := by decide +kernel
theorem fusedMap3563swap_checked : acceptsGraphIso
    (fused (graph core3563) (root 8) 6 0) DegreeTwoThreeSpectrum5106.graph fusedMap3563swap=true := by decide +kernel
theorem certified3563swap : Certified (graph core3563) (root 8) 6 0 :=
  of_native_maps core3563 DegreeTwoThreeSpectrum5925.graph DegreeTwoThreeSpectrum5106.graph
    sourceMap3563swap fusedMap3563swap sourceMap3563swap_checked fusedMap3563swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3563
#print axioms sourceMap3563swap_checked
#print axioms fusedMap3563swap_checked
#print axioms certified3563swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
