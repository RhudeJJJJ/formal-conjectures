/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1536 : Family 10 := level10.get ⟨413,by decide⟩
def sourceMap1536 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,7,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1536 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1536_checked : acceptsGraphIso
    (source (graph core1536) (root 10) 0 2) DegreeTwoThreeSpectrum2890.graph sourceMap1536=true := by decide +kernel
theorem fusedMap1536_checked : acceptsGraphIso
    (fused (graph core1536) (root 10) 0 2) DegreeTwoThreeSpectrum2928.graph fusedMap1536=true := by decide +kernel
theorem certified1536 : Certified (graph core1536) (root 10) 0 2 :=
  of_native_maps core1536 DegreeTwoThreeSpectrum2890.graph DegreeTwoThreeSpectrum2928.graph
    sourceMap1536 fusedMap1536 sourceMap1536_checked fusedMap1536_checked
    DegreeTwoThreeFiniteComparisons.comparison1536
#print axioms sourceMap1536_checked
#print axioms fusedMap1536_checked
#print axioms certified1536
def sourceMap1536swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,7,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1536swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,13,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1536swap_checked : acceptsGraphIso
    (source (graph core1536) (root 10) 2 0) DegreeTwoThreeSpectrum2890.graph sourceMap1536swap=true := by decide +kernel
theorem fusedMap1536swap_checked : acceptsGraphIso
    (fused (graph core1536) (root 10) 2 0) DegreeTwoThreeSpectrum2928.graph fusedMap1536swap=true := by decide +kernel
theorem certified1536swap : Certified (graph core1536) (root 10) 2 0 :=
  of_native_maps core1536 DegreeTwoThreeSpectrum2890.graph DegreeTwoThreeSpectrum2928.graph
    sourceMap1536swap fusedMap1536swap sourceMap1536swap_checked fusedMap1536swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1536
#print axioms sourceMap1536swap_checked
#print axioms fusedMap1536swap_checked
#print axioms certified1536swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
