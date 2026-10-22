/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1604 : Family 10 := level10.get ⟨612,by decide⟩
def sourceMap1604 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1604 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1604_checked : acceptsGraphIso
    (source (graph core1604) (root 10) 0 2) DegreeTwoThreeSpectrum3270.graph sourceMap1604=true := by decide +kernel
theorem fusedMap1604_checked : acceptsGraphIso
    (fused (graph core1604) (root 10) 0 2) DegreeTwoThreeSpectrum2557.graph fusedMap1604=true := by decide +kernel
theorem certified1604 : Certified (graph core1604) (root 10) 0 2 :=
  of_native_maps core1604 DegreeTwoThreeSpectrum3270.graph DegreeTwoThreeSpectrum2557.graph
    sourceMap1604 fusedMap1604 sourceMap1604_checked fusedMap1604_checked
    DegreeTwoThreeFiniteComparisons.comparison1604
#print axioms sourceMap1604_checked
#print axioms fusedMap1604_checked
#print axioms certified1604
def sourceMap1604swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1604swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1604swap_checked : acceptsGraphIso
    (source (graph core1604) (root 10) 2 0) DegreeTwoThreeSpectrum3270.graph sourceMap1604swap=true := by decide +kernel
theorem fusedMap1604swap_checked : acceptsGraphIso
    (fused (graph core1604) (root 10) 2 0) DegreeTwoThreeSpectrum2557.graph fusedMap1604swap=true := by decide +kernel
theorem certified1604swap : Certified (graph core1604) (root 10) 2 0 :=
  of_native_maps core1604 DegreeTwoThreeSpectrum3270.graph DegreeTwoThreeSpectrum2557.graph
    sourceMap1604swap fusedMap1604swap sourceMap1604swap_checked fusedMap1604swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1604
#print axioms sourceMap1604swap_checked
#print axioms fusedMap1604swap_checked
#print axioms certified1604swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
