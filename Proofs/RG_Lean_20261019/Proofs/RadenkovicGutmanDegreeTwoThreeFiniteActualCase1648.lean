/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1648 : Family 10 := level10.get ⟨742,by decide⟩
def sourceMap1648 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1648 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1648_checked : acceptsGraphIso
    (source (graph core1648) (root 10) 0 2) DegreeTwoThreeSpectrum3502.graph sourceMap1648=true := by decide +kernel
theorem fusedMap1648_checked : acceptsGraphIso
    (fused (graph core1648) (root 10) 0 2) DegreeTwoThreeSpectrum2705.graph fusedMap1648=true := by decide +kernel
theorem certified1648 : Certified (graph core1648) (root 10) 0 2 :=
  of_native_maps core1648 DegreeTwoThreeSpectrum3502.graph DegreeTwoThreeSpectrum2705.graph
    sourceMap1648 fusedMap1648 sourceMap1648_checked fusedMap1648_checked
    DegreeTwoThreeFiniteComparisons.comparison1648
#print axioms sourceMap1648_checked
#print axioms fusedMap1648_checked
#print axioms certified1648
def sourceMap1648swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1648swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1648swap_checked : acceptsGraphIso
    (source (graph core1648) (root 10) 2 0) DegreeTwoThreeSpectrum3502.graph sourceMap1648swap=true := by decide +kernel
theorem fusedMap1648swap_checked : acceptsGraphIso
    (fused (graph core1648) (root 10) 2 0) DegreeTwoThreeSpectrum2705.graph fusedMap1648swap=true := by decide +kernel
theorem certified1648swap : Certified (graph core1648) (root 10) 2 0 :=
  of_native_maps core1648 DegreeTwoThreeSpectrum3502.graph DegreeTwoThreeSpectrum2705.graph
    sourceMap1648swap fusedMap1648swap sourceMap1648swap_checked fusedMap1648swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1648
#print axioms sourceMap1648swap_checked
#print axioms fusedMap1648swap_checked
#print axioms certified1648swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
