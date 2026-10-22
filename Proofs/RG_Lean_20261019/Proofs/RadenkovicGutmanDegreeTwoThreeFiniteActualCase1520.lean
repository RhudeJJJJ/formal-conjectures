/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1520 : Family 10 := level10.get ⟨360,by decide⟩
def sourceMap1520 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1520 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,12,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1520_checked : acceptsGraphIso
    (source (graph core1520) (root 10) 0 2) DegreeTwoThreeSpectrum2801.graph sourceMap1520=true := by decide +kernel
theorem fusedMap1520_checked : acceptsGraphIso
    (fused (graph core1520) (root 10) 0 2) DegreeTwoThreeSpectrum2813.graph fusedMap1520=true := by decide +kernel
theorem certified1520 : Certified (graph core1520) (root 10) 0 2 :=
  of_native_maps core1520 DegreeTwoThreeSpectrum2801.graph DegreeTwoThreeSpectrum2813.graph
    sourceMap1520 fusedMap1520 sourceMap1520_checked fusedMap1520_checked
    DegreeTwoThreeFiniteComparisons.comparison1520
#print axioms sourceMap1520_checked
#print axioms fusedMap1520_checked
#print axioms certified1520
def sourceMap1520swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1520swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,12,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1520swap_checked : acceptsGraphIso
    (source (graph core1520) (root 10) 2 0) DegreeTwoThreeSpectrum2801.graph sourceMap1520swap=true := by decide +kernel
theorem fusedMap1520swap_checked : acceptsGraphIso
    (fused (graph core1520) (root 10) 2 0) DegreeTwoThreeSpectrum2813.graph fusedMap1520swap=true := by decide +kernel
theorem certified1520swap : Certified (graph core1520) (root 10) 2 0 :=
  of_native_maps core1520 DegreeTwoThreeSpectrum2801.graph DegreeTwoThreeSpectrum2813.graph
    sourceMap1520swap fusedMap1520swap sourceMap1520swap_checked fusedMap1520swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1520
#print axioms sourceMap1520swap_checked
#print axioms fusedMap1520swap_checked
#print axioms certified1520swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
