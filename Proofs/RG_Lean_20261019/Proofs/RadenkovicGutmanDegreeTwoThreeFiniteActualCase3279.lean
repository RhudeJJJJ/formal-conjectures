/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3279 : Family 9 := level9.get ⟨172,by decide⟩
def sourceMap3279 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3279 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3279_checked : acceptsGraphIso
    (source (graph core3279) (root 9) 0 5) DegreeTwoThreeSpectrum5296.graph sourceMap3279=true := by decide +kernel
theorem fusedMap3279_checked : acceptsGraphIso
    (fused (graph core3279) (root 9) 0 5) DegreeTwoThreeSpectrum5297.graph fusedMap3279=true := by decide +kernel
theorem certified3279 : Certified (graph core3279) (root 9) 0 5 :=
  of_native_maps core3279 DegreeTwoThreeSpectrum5296.graph DegreeTwoThreeSpectrum5297.graph
    sourceMap3279 fusedMap3279 sourceMap3279_checked fusedMap3279_checked
    DegreeTwoThreeFiniteComparisons.comparison3279
#print axioms sourceMap3279_checked
#print axioms fusedMap3279_checked
#print axioms certified3279
def sourceMap3279swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3279swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3279swap_checked : acceptsGraphIso
    (source (graph core3279) (root 9) 5 0) DegreeTwoThreeSpectrum5296.graph sourceMap3279swap=true := by decide +kernel
theorem fusedMap3279swap_checked : acceptsGraphIso
    (fused (graph core3279) (root 9) 5 0) DegreeTwoThreeSpectrum5297.graph fusedMap3279swap=true := by decide +kernel
theorem certified3279swap : Certified (graph core3279) (root 9) 5 0 :=
  of_native_maps core3279 DegreeTwoThreeSpectrum5296.graph DegreeTwoThreeSpectrum5297.graph
    sourceMap3279swap fusedMap3279swap sourceMap3279swap_checked fusedMap3279swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3279
#print axioms sourceMap3279swap_checked
#print axioms fusedMap3279swap_checked
#print axioms certified3279swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
