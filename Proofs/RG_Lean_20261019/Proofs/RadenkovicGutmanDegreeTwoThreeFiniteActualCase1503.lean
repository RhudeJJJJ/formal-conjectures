/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1503 : Family 10 := level10.get ⟨301,by decide⟩
def sourceMap1503 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,13,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1503 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1503_checked : acceptsGraphIso
    (source (graph core1503) (root 10) 0 2) DegreeTwoThreeSpectrum2683.graph sourceMap1503=true := by decide +kernel
theorem fusedMap1503_checked : acceptsGraphIso
    (fused (graph core1503) (root 10) 0 2) DegreeTwoThreeSpectrum2688.graph fusedMap1503=true := by decide +kernel
theorem certified1503 : Certified (graph core1503) (root 10) 0 2 :=
  of_native_maps core1503 DegreeTwoThreeSpectrum2683.graph DegreeTwoThreeSpectrum2688.graph
    sourceMap1503 fusedMap1503 sourceMap1503_checked fusedMap1503_checked
    DegreeTwoThreeFiniteComparisons.comparison1503
#print axioms sourceMap1503_checked
#print axioms fusedMap1503_checked
#print axioms certified1503
def sourceMap1503swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,7,0,1,2,3,4,5,6,14,12,9,10,11,13] (sourceLabel 10 2 0 v)
def fusedMap1503swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1503swap_checked : acceptsGraphIso
    (source (graph core1503) (root 10) 2 0) DegreeTwoThreeSpectrum2683.graph sourceMap1503swap=true := by decide +kernel
theorem fusedMap1503swap_checked : acceptsGraphIso
    (fused (graph core1503) (root 10) 2 0) DegreeTwoThreeSpectrum2688.graph fusedMap1503swap=true := by decide +kernel
theorem certified1503swap : Certified (graph core1503) (root 10) 2 0 :=
  of_native_maps core1503 DegreeTwoThreeSpectrum2683.graph DegreeTwoThreeSpectrum2688.graph
    sourceMap1503swap fusedMap1503swap sourceMap1503swap_checked fusedMap1503swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1503
#print axioms sourceMap1503swap_checked
#print axioms fusedMap1503swap_checked
#print axioms certified1503swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
