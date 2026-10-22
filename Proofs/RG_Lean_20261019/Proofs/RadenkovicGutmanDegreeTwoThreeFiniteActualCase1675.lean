/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1675 : Family 10 := level10.get ⟨815,by decide⟩
def sourceMap1675 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,10,11,12,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1675 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1675_checked : acceptsGraphIso
    (source (graph core1675) (root 10) 0 2) DegreeTwoThreeSpectrum3598.graph sourceMap1675=true := by decide +kernel
theorem fusedMap1675_checked : acceptsGraphIso
    (fused (graph core1675) (root 10) 0 2) DegreeTwoThreeSpectrum2786.graph fusedMap1675=true := by decide +kernel
theorem certified1675 : Certified (graph core1675) (root 10) 0 2 :=
  of_native_maps core1675 DegreeTwoThreeSpectrum3598.graph DegreeTwoThreeSpectrum2786.graph
    sourceMap1675 fusedMap1675 sourceMap1675_checked fusedMap1675_checked
    DegreeTwoThreeFiniteComparisons.comparison1675
#print axioms sourceMap1675_checked
#print axioms fusedMap1675_checked
#print axioms certified1675
def sourceMap1675swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,10,11,7,8,9,12] (sourceLabel 10 2 0 v)
def fusedMap1675swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1675swap_checked : acceptsGraphIso
    (source (graph core1675) (root 10) 2 0) DegreeTwoThreeSpectrum3598.graph sourceMap1675swap=true := by decide +kernel
theorem fusedMap1675swap_checked : acceptsGraphIso
    (fused (graph core1675) (root 10) 2 0) DegreeTwoThreeSpectrum2786.graph fusedMap1675swap=true := by decide +kernel
theorem certified1675swap : Certified (graph core1675) (root 10) 2 0 :=
  of_native_maps core1675 DegreeTwoThreeSpectrum3598.graph DegreeTwoThreeSpectrum2786.graph
    sourceMap1675swap fusedMap1675swap sourceMap1675swap_checked fusedMap1675swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1675
#print axioms sourceMap1675swap_checked
#print axioms fusedMap1675swap_checked
#print axioms certified1675swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
