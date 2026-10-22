/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1542 : Family 10 := level10.get ⟨425,by decide⟩
def sourceMap1542 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,8,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1542 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1542_checked : acceptsGraphIso
    (source (graph core1542) (root 10) 0 2) DegreeTwoThreeSpectrum2832.graph sourceMap1542=true := by decide +kernel
theorem fusedMap1542_checked : acceptsGraphIso
    (fused (graph core1542) (root 10) 0 2) DegreeTwoThreeSpectrum2936.graph fusedMap1542=true := by decide +kernel
theorem certified1542 : Certified (graph core1542) (root 10) 0 2 :=
  of_native_maps core1542 DegreeTwoThreeSpectrum2832.graph DegreeTwoThreeSpectrum2936.graph
    sourceMap1542 fusedMap1542 sourceMap1542_checked fusedMap1542_checked
    DegreeTwoThreeFiniteComparisons.comparison1542
#print axioms sourceMap1542_checked
#print axioms fusedMap1542_checked
#print axioms certified1542
def sourceMap1542swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,5,6,7,2,3,4,8] (sourceLabel 10 2 0 v)
def fusedMap1542swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1542swap_checked : acceptsGraphIso
    (source (graph core1542) (root 10) 2 0) DegreeTwoThreeSpectrum2832.graph sourceMap1542swap=true := by decide +kernel
theorem fusedMap1542swap_checked : acceptsGraphIso
    (fused (graph core1542) (root 10) 2 0) DegreeTwoThreeSpectrum2936.graph fusedMap1542swap=true := by decide +kernel
theorem certified1542swap : Certified (graph core1542) (root 10) 2 0 :=
  of_native_maps core1542 DegreeTwoThreeSpectrum2832.graph DegreeTwoThreeSpectrum2936.graph
    sourceMap1542swap fusedMap1542swap sourceMap1542swap_checked fusedMap1542swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1542
#print axioms sourceMap1542swap_checked
#print axioms fusedMap1542swap_checked
#print axioms certified1542swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
