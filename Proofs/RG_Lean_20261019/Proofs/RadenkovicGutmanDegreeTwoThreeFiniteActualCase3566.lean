/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3566 : Family 8 := level8.get ⟨102,by decide⟩
def sourceMap3566 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3566 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3566_checked : acceptsGraphIso
    (source (graph core3566) (root 8) 0 6) DegreeTwoThreeSpectrum5175.graph sourceMap3566=true := by decide +kernel
theorem fusedMap3566_checked : acceptsGraphIso
    (fused (graph core3566) (root 8) 0 6) DegreeTwoThreeSpectrum5177.graph fusedMap3566=true := by decide +kernel
theorem certified3566 : Certified (graph core3566) (root 8) 0 6 :=
  of_native_maps core3566 DegreeTwoThreeSpectrum5175.graph DegreeTwoThreeSpectrum5177.graph
    sourceMap3566 fusedMap3566 sourceMap3566_checked fusedMap3566_checked
    DegreeTwoThreeFiniteComparisons.comparison3566
#print axioms sourceMap3566_checked
#print axioms fusedMap3566_checked
#print axioms certified3566
def sourceMap3566swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3566swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3566swap_checked : acceptsGraphIso
    (source (graph core3566) (root 8) 6 0) DegreeTwoThreeSpectrum5175.graph sourceMap3566swap=true := by decide +kernel
theorem fusedMap3566swap_checked : acceptsGraphIso
    (fused (graph core3566) (root 8) 6 0) DegreeTwoThreeSpectrum5177.graph fusedMap3566swap=true := by decide +kernel
theorem certified3566swap : Certified (graph core3566) (root 8) 6 0 :=
  of_native_maps core3566 DegreeTwoThreeSpectrum5175.graph DegreeTwoThreeSpectrum5177.graph
    sourceMap3566swap fusedMap3566swap sourceMap3566swap_checked fusedMap3566swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3566
#print axioms sourceMap3566swap_checked
#print axioms fusedMap3566swap_checked
#print axioms certified3566swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
