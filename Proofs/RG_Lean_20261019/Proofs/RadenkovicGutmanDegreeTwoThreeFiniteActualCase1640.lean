/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1640 : Family 10 := level10.get ⟨718,by decide⟩
def sourceMap1640 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1640 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1640_checked : acceptsGraphIso
    (source (graph core1640) (root 10) 0 2) DegreeTwoThreeSpectrum3453.graph sourceMap1640=true := by decide +kernel
theorem fusedMap1640_checked : acceptsGraphIso
    (fused (graph core1640) (root 10) 0 2) DegreeTwoThreeSpectrum2677.graph fusedMap1640=true := by decide +kernel
theorem certified1640 : Certified (graph core1640) (root 10) 0 2 :=
  of_native_maps core1640 DegreeTwoThreeSpectrum3453.graph DegreeTwoThreeSpectrum2677.graph
    sourceMap1640 fusedMap1640 sourceMap1640_checked fusedMap1640_checked
    DegreeTwoThreeFiniteComparisons.comparison1640
#print axioms sourceMap1640_checked
#print axioms fusedMap1640_checked
#print axioms certified1640
def sourceMap1640swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1640swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1640swap_checked : acceptsGraphIso
    (source (graph core1640) (root 10) 2 0) DegreeTwoThreeSpectrum3453.graph sourceMap1640swap=true := by decide +kernel
theorem fusedMap1640swap_checked : acceptsGraphIso
    (fused (graph core1640) (root 10) 2 0) DegreeTwoThreeSpectrum2677.graph fusedMap1640swap=true := by decide +kernel
theorem certified1640swap : Certified (graph core1640) (root 10) 2 0 :=
  of_native_maps core1640 DegreeTwoThreeSpectrum3453.graph DegreeTwoThreeSpectrum2677.graph
    sourceMap1640swap fusedMap1640swap sourceMap1640swap_checked fusedMap1640swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1640
#print axioms sourceMap1640swap_checked
#print axioms fusedMap1640swap_checked
#print axioms certified1640swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
