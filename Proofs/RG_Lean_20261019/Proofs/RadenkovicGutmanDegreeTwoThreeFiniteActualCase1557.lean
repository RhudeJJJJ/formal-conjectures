/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1557 : Family 10 := level10.get ⟨474,by decide⟩
def sourceMap1557 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,7,8,9,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1557 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1557_checked : acceptsGraphIso
    (source (graph core1557) (root 10) 0 2) DegreeTwoThreeSpectrum2880.graph sourceMap1557=true := by decide +kernel
theorem fusedMap1557_checked : acceptsGraphIso
    (fused (graph core1557) (root 10) 0 2) DegreeTwoThreeSpectrum2990.graph fusedMap1557=true := by decide +kernel
theorem certified1557 : Certified (graph core1557) (root 10) 0 2 :=
  of_native_maps core1557 DegreeTwoThreeSpectrum2880.graph DegreeTwoThreeSpectrum2990.graph
    sourceMap1557 fusedMap1557 sourceMap1557_checked fusedMap1557_checked
    DegreeTwoThreeFiniteComparisons.comparison1557
#print axioms sourceMap1557_checked
#print axioms fusedMap1557_checked
#print axioms certified1557
def sourceMap1557swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,7,8,9,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1557swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,6,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1557swap_checked : acceptsGraphIso
    (source (graph core1557) (root 10) 2 0) DegreeTwoThreeSpectrum2880.graph sourceMap1557swap=true := by decide +kernel
theorem fusedMap1557swap_checked : acceptsGraphIso
    (fused (graph core1557) (root 10) 2 0) DegreeTwoThreeSpectrum2990.graph fusedMap1557swap=true := by decide +kernel
theorem certified1557swap : Certified (graph core1557) (root 10) 2 0 :=
  of_native_maps core1557 DegreeTwoThreeSpectrum2880.graph DegreeTwoThreeSpectrum2990.graph
    sourceMap1557swap fusedMap1557swap sourceMap1557swap_checked fusedMap1557swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1557
#print axioms sourceMap1557swap_checked
#print axioms fusedMap1557swap_checked
#print axioms certified1557swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
