/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1436 : Family 10 := level10.get ⟨43,by decide⟩
def sourceMap1436 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,7,3,4,5] (sourceLabel 10 0 2 v)
def fusedMap1436 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,7,3,4,5,6] (fusedLabel 10 0 2 v)
theorem sourceMap1436_checked : acceptsGraphIso
    (source (graph core1436) (root 10) 0 2) DegreeTwoThreeSpectrum2392.graph sourceMap1436=true := by decide +kernel
theorem fusedMap1436_checked : acceptsGraphIso
    (fused (graph core1436) (root 10) 0 2) DegreeTwoThreeSpectrum2426.graph fusedMap1436=true := by decide +kernel
theorem certified1436 : Certified (graph core1436) (root 10) 0 2 :=
  of_native_maps core1436 DegreeTwoThreeSpectrum2392.graph DegreeTwoThreeSpectrum2426.graph
    sourceMap1436 fusedMap1436 sourceMap1436_checked fusedMap1436_checked
    DegreeTwoThreeFiniteComparisons.comparison1436
#print axioms sourceMap1436_checked
#print axioms fusedMap1436_checked
#print axioms certified1436
def sourceMap1436swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,6,3,4,5,7] (sourceLabel 10 2 0 v)
def fusedMap1436swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![2,1,0,8,9,10,11,12,13,14,7,3,4,5,6] (fusedLabel 10 2 0 v)
theorem sourceMap1436swap_checked : acceptsGraphIso
    (source (graph core1436) (root 10) 2 0) DegreeTwoThreeSpectrum2392.graph sourceMap1436swap=true := by decide +kernel
theorem fusedMap1436swap_checked : acceptsGraphIso
    (fused (graph core1436) (root 10) 2 0) DegreeTwoThreeSpectrum2426.graph fusedMap1436swap=true := by decide +kernel
theorem certified1436swap : Certified (graph core1436) (root 10) 2 0 :=
  of_native_maps core1436 DegreeTwoThreeSpectrum2392.graph DegreeTwoThreeSpectrum2426.graph
    sourceMap1436swap fusedMap1436swap sourceMap1436swap_checked fusedMap1436swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1436
#print axioms sourceMap1436swap_checked
#print axioms fusedMap1436swap_checked
#print axioms certified1436swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
