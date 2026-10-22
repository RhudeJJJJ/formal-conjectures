/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1524 : Family 10 := level10.get ⟨370,by decide⟩
def sourceMap1524 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1524 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1524_checked : acceptsGraphIso
    (source (graph core1524) (root 10) 0 2) DegreeTwoThreeSpectrum2823.graph sourceMap1524=true := by decide +kernel
theorem fusedMap1524_checked : acceptsGraphIso
    (fused (graph core1524) (root 10) 0 2) DegreeTwoThreeSpectrum2825.graph fusedMap1524=true := by decide +kernel
theorem certified1524 : Certified (graph core1524) (root 10) 0 2 :=
  of_native_maps core1524 DegreeTwoThreeSpectrum2823.graph DegreeTwoThreeSpectrum2825.graph
    sourceMap1524 fusedMap1524 sourceMap1524_checked fusedMap1524_checked
    DegreeTwoThreeFiniteComparisons.comparison1524
#print axioms sourceMap1524_checked
#print axioms fusedMap1524_checked
#print axioms certified1524
def sourceMap1524swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1524swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1524swap_checked : acceptsGraphIso
    (source (graph core1524) (root 10) 2 0) DegreeTwoThreeSpectrum2823.graph sourceMap1524swap=true := by decide +kernel
theorem fusedMap1524swap_checked : acceptsGraphIso
    (fused (graph core1524) (root 10) 2 0) DegreeTwoThreeSpectrum2825.graph fusedMap1524swap=true := by decide +kernel
theorem certified1524swap : Certified (graph core1524) (root 10) 2 0 :=
  of_native_maps core1524 DegreeTwoThreeSpectrum2823.graph DegreeTwoThreeSpectrum2825.graph
    sourceMap1524swap fusedMap1524swap sourceMap1524swap_checked fusedMap1524swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1524
#print axioms sourceMap1524swap_checked
#print axioms fusedMap1524swap_checked
#print axioms certified1524swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
