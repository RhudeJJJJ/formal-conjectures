/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1653 : Family 10 := level10.get ⟨756,by decide⟩
def sourceMap1653 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1653 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1653_checked : acceptsGraphIso
    (source (graph core1653) (root 10) 0 2) DegreeTwoThreeSpectrum3522.graph sourceMap1653=true := by decide +kernel
theorem fusedMap1653_checked : acceptsGraphIso
    (fused (graph core1653) (root 10) 0 2) DegreeTwoThreeSpectrum2718.graph fusedMap1653=true := by decide +kernel
theorem certified1653 : Certified (graph core1653) (root 10) 0 2 :=
  of_native_maps core1653 DegreeTwoThreeSpectrum3522.graph DegreeTwoThreeSpectrum2718.graph
    sourceMap1653 fusedMap1653 sourceMap1653_checked fusedMap1653_checked
    DegreeTwoThreeFiniteComparisons.comparison1653
#print axioms sourceMap1653_checked
#print axioms fusedMap1653_checked
#print axioms certified1653
def sourceMap1653swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1653swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1653swap_checked : acceptsGraphIso
    (source (graph core1653) (root 10) 2 0) DegreeTwoThreeSpectrum3522.graph sourceMap1653swap=true := by decide +kernel
theorem fusedMap1653swap_checked : acceptsGraphIso
    (fused (graph core1653) (root 10) 2 0) DegreeTwoThreeSpectrum2718.graph fusedMap1653swap=true := by decide +kernel
theorem certified1653swap : Certified (graph core1653) (root 10) 2 0 :=
  of_native_maps core1653 DegreeTwoThreeSpectrum3522.graph DegreeTwoThreeSpectrum2718.graph
    sourceMap1653swap fusedMap1653swap sourceMap1653swap_checked fusedMap1653swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1653
#print axioms sourceMap1653swap_checked
#print axioms fusedMap1653swap_checked
#print axioms certified1653swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
