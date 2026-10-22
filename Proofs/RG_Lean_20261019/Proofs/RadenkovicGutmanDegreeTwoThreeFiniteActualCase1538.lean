/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1538 : Family 10 := level10.get ⟨419,by decide⟩
def sourceMap1538 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,8,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1538 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,12,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1538_checked : acceptsGraphIso
    (source (graph core1538) (root 10) 0 2) DegreeTwoThreeSpectrum2882.graph sourceMap1538=true := by decide +kernel
theorem fusedMap1538_checked : acceptsGraphIso
    (fused (graph core1538) (root 10) 0 2) DegreeTwoThreeSpectrum2938.graph fusedMap1538=true := by decide +kernel
theorem certified1538 : Certified (graph core1538) (root 10) 0 2 :=
  of_native_maps core1538 DegreeTwoThreeSpectrum2882.graph DegreeTwoThreeSpectrum2938.graph
    sourceMap1538 fusedMap1538 sourceMap1538_checked fusedMap1538_checked
    DegreeTwoThreeFiniteComparisons.comparison1538
#print axioms sourceMap1538_checked
#print axioms fusedMap1538_checked
#print axioms certified1538
def sourceMap1538swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,7,8,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1538swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,12,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1538swap_checked : acceptsGraphIso
    (source (graph core1538) (root 10) 2 0) DegreeTwoThreeSpectrum2882.graph sourceMap1538swap=true := by decide +kernel
theorem fusedMap1538swap_checked : acceptsGraphIso
    (fused (graph core1538) (root 10) 2 0) DegreeTwoThreeSpectrum2938.graph fusedMap1538swap=true := by decide +kernel
theorem certified1538swap : Certified (graph core1538) (root 10) 2 0 :=
  of_native_maps core1538 DegreeTwoThreeSpectrum2882.graph DegreeTwoThreeSpectrum2938.graph
    sourceMap1538swap fusedMap1538swap sourceMap1538swap_checked fusedMap1538swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1538
#print axioms sourceMap1538swap_checked
#print axioms fusedMap1538swap_checked
#print axioms certified1538swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
