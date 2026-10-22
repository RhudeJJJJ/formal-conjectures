/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3736 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap3736 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 10) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,10,3,2,1,0,11,12,13,14,15,16] (sourceLabel 5 0 9 v)
def fusedMap3736 : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 0 9 v)
theorem sourceMap3736_checked : acceptsGraphIso
    (source (graph core3736) (root 5) 0 9) DegreeTwoThreeSpectrum5232.graph sourceMap3736=true := by decide +kernel
theorem fusedMap3736_checked : acceptsGraphIso
    (fused (graph core3736) (root 5) 0 9) DegreeTwoThreeSpectrum4973.graph fusedMap3736=true := by decide +kernel
theorem certified3736 : Certified (graph core3736) (root 5) 0 9 :=
  of_native_maps core3736 DegreeTwoThreeSpectrum5232.graph DegreeTwoThreeSpectrum4973.graph
    sourceMap3736 fusedMap3736 sourceMap3736_checked fusedMap3736_checked
    DegreeTwoThreeFiniteComparisons.comparison3736
#print axioms sourceMap3736_checked
#print axioms fusedMap3736_checked
#print axioms certified3736
def sourceMap3736swap : (Vertices 5 ⊕ Fin 10 ⊕ Fin 1) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,11,12,13,14,15,16,10] (sourceLabel 5 9 0 v)
def fusedMap3736swap : (Vertices 5 ⊕ Fin 11) → Fin 17 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 5 9 0 v)
theorem sourceMap3736swap_checked : acceptsGraphIso
    (source (graph core3736) (root 5) 9 0) DegreeTwoThreeSpectrum5232.graph sourceMap3736swap=true := by decide +kernel
theorem fusedMap3736swap_checked : acceptsGraphIso
    (fused (graph core3736) (root 5) 9 0) DegreeTwoThreeSpectrum4973.graph fusedMap3736swap=true := by decide +kernel
theorem certified3736swap : Certified (graph core3736) (root 5) 9 0 :=
  of_native_maps core3736 DegreeTwoThreeSpectrum5232.graph DegreeTwoThreeSpectrum4973.graph
    sourceMap3736swap fusedMap3736swap sourceMap3736swap_checked fusedMap3736swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3736
#print axioms sourceMap3736swap_checked
#print axioms fusedMap3736swap_checked
#print axioms certified3736swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
