/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1496 : Family 10 := level10.get ⟨277,by decide⟩
def sourceMap1496 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1496 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,12,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1496_checked : acceptsGraphIso
    (source (graph core1496) (root 10) 0 2) DegreeTwoThreeSpectrum2632.graph sourceMap1496=true := by decide +kernel
theorem fusedMap1496_checked : acceptsGraphIso
    (fused (graph core1496) (root 10) 0 2) DegreeTwoThreeSpectrum2644.graph fusedMap1496=true := by decide +kernel
theorem certified1496 : Certified (graph core1496) (root 10) 0 2 :=
  of_native_maps core1496 DegreeTwoThreeSpectrum2632.graph DegreeTwoThreeSpectrum2644.graph
    sourceMap1496 fusedMap1496 sourceMap1496_checked fusedMap1496_checked
    DegreeTwoThreeFiniteComparisons.comparison1496
#print axioms sourceMap1496_checked
#print axioms fusedMap1496_checked
#print axioms certified1496
def sourceMap1496swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1496swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,12,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1496swap_checked : acceptsGraphIso
    (source (graph core1496) (root 10) 2 0) DegreeTwoThreeSpectrum2632.graph sourceMap1496swap=true := by decide +kernel
theorem fusedMap1496swap_checked : acceptsGraphIso
    (fused (graph core1496) (root 10) 2 0) DegreeTwoThreeSpectrum2644.graph fusedMap1496swap=true := by decide +kernel
theorem certified1496swap : Certified (graph core1496) (root 10) 2 0 :=
  of_native_maps core1496 DegreeTwoThreeSpectrum2632.graph DegreeTwoThreeSpectrum2644.graph
    sourceMap1496swap fusedMap1496swap sourceMap1496swap_checked fusedMap1496swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1496
#print axioms sourceMap1496swap_checked
#print axioms fusedMap1496swap_checked
#print axioms certified1496swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
