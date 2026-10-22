/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1580 : Family 10 := level10.get ⟨544,by decide⟩
def sourceMap1580 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1580 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1580_checked : acceptsGraphIso
    (source (graph core1580) (root 10) 0 2) DegreeTwoThreeSpectrum3140.graph sourceMap1580=true := by decide +kernel
theorem fusedMap1580_checked : acceptsGraphIso
    (fused (graph core1580) (root 10) 0 2) DegreeTwoThreeSpectrum2481.graph fusedMap1580=true := by decide +kernel
theorem certified1580 : Certified (graph core1580) (root 10) 0 2 :=
  of_native_maps core1580 DegreeTwoThreeSpectrum3140.graph DegreeTwoThreeSpectrum2481.graph
    sourceMap1580 fusedMap1580 sourceMap1580_checked fusedMap1580_checked
    DegreeTwoThreeFiniteComparisons.comparison1580
#print axioms sourceMap1580_checked
#print axioms fusedMap1580_checked
#print axioms certified1580
def sourceMap1580swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1580swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1580swap_checked : acceptsGraphIso
    (source (graph core1580) (root 10) 2 0) DegreeTwoThreeSpectrum3140.graph sourceMap1580swap=true := by decide +kernel
theorem fusedMap1580swap_checked : acceptsGraphIso
    (fused (graph core1580) (root 10) 2 0) DegreeTwoThreeSpectrum2481.graph fusedMap1580swap=true := by decide +kernel
theorem certified1580swap : Certified (graph core1580) (root 10) 2 0 :=
  of_native_maps core1580 DegreeTwoThreeSpectrum3140.graph DegreeTwoThreeSpectrum2481.graph
    sourceMap1580swap fusedMap1580swap sourceMap1580swap_checked fusedMap1580swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1580
#print axioms sourceMap1580swap_checked
#print axioms fusedMap1580swap_checked
#print axioms certified1580swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
