/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1477 : Family 10 := level10.get ⟨209,by decide⟩
def sourceMap1477 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1477 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1477_checked : acceptsGraphIso
    (source (graph core1477) (root 10) 0 2) DegreeTwoThreeSpectrum2491.graph sourceMap1477=true := by decide +kernel
theorem fusedMap1477_checked : acceptsGraphIso
    (fused (graph core1477) (root 10) 0 2) DegreeTwoThreeSpectrum2493.graph fusedMap1477=true := by decide +kernel
theorem certified1477 : Certified (graph core1477) (root 10) 0 2 :=
  of_native_maps core1477 DegreeTwoThreeSpectrum2491.graph DegreeTwoThreeSpectrum2493.graph
    sourceMap1477 fusedMap1477 sourceMap1477_checked fusedMap1477_checked
    DegreeTwoThreeFiniteComparisons.comparison1477
#print axioms sourceMap1477_checked
#print axioms fusedMap1477_checked
#print axioms certified1477
def sourceMap1477swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1477swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1477swap_checked : acceptsGraphIso
    (source (graph core1477) (root 10) 2 0) DegreeTwoThreeSpectrum2491.graph sourceMap1477swap=true := by decide +kernel
theorem fusedMap1477swap_checked : acceptsGraphIso
    (fused (graph core1477) (root 10) 2 0) DegreeTwoThreeSpectrum2493.graph fusedMap1477swap=true := by decide +kernel
theorem certified1477swap : Certified (graph core1477) (root 10) 2 0 :=
  of_native_maps core1477 DegreeTwoThreeSpectrum2491.graph DegreeTwoThreeSpectrum2493.graph
    sourceMap1477swap fusedMap1477swap sourceMap1477swap_checked fusedMap1477swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1477
#print axioms sourceMap1477swap_checked
#print axioms fusedMap1477swap_checked
#print axioms certified1477swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
