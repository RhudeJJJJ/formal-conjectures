/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1614 : Family 10 := level10.get ⟨646,by decide⟩
def sourceMap1614 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1614 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1614_checked : acceptsGraphIso
    (source (graph core1614) (root 10) 0 2) DegreeTwoThreeSpectrum3343.graph sourceMap1614=true := by decide +kernel
theorem fusedMap1614_checked : acceptsGraphIso
    (fused (graph core1614) (root 10) 0 2) DegreeTwoThreeSpectrum2589.graph fusedMap1614=true := by decide +kernel
theorem certified1614 : Certified (graph core1614) (root 10) 0 2 :=
  of_native_maps core1614 DegreeTwoThreeSpectrum3343.graph DegreeTwoThreeSpectrum2589.graph
    sourceMap1614 fusedMap1614 sourceMap1614_checked fusedMap1614_checked
    DegreeTwoThreeFiniteComparisons.comparison1614
#print axioms sourceMap1614_checked
#print axioms fusedMap1614_checked
#print axioms certified1614
def sourceMap1614swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1614swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1614swap_checked : acceptsGraphIso
    (source (graph core1614) (root 10) 2 0) DegreeTwoThreeSpectrum3343.graph sourceMap1614swap=true := by decide +kernel
theorem fusedMap1614swap_checked : acceptsGraphIso
    (fused (graph core1614) (root 10) 2 0) DegreeTwoThreeSpectrum2589.graph fusedMap1614swap=true := by decide +kernel
theorem certified1614swap : Certified (graph core1614) (root 10) 2 0 :=
  of_native_maps core1614 DegreeTwoThreeSpectrum3343.graph DegreeTwoThreeSpectrum2589.graph
    sourceMap1614swap fusedMap1614swap sourceMap1614swap_checked fusedMap1614swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1614
#print axioms sourceMap1614swap_checked
#print axioms fusedMap1614swap_checked
#print axioms certified1614swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
