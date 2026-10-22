/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1740 : Family 10 := level10.get ⟨976,by decide⟩
def sourceMap1740 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1740 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1740_checked : acceptsGraphIso
    (source (graph core1740) (root 10) 0 2) DegreeTwoThreeSpectrum2603.graph sourceMap1740=true := by decide +kernel
theorem fusedMap1740_checked : acceptsGraphIso
    (fused (graph core1740) (root 10) 0 2) DegreeTwoThreeSpectrum2602.graph fusedMap1740=true := by decide +kernel
theorem certified1740 : Certified (graph core1740) (root 10) 0 2 :=
  of_native_maps core1740 DegreeTwoThreeSpectrum2603.graph DegreeTwoThreeSpectrum2602.graph
    sourceMap1740 fusedMap1740 sourceMap1740_checked fusedMap1740_checked
    DegreeTwoThreeFiniteComparisons.comparison1740
#print axioms sourceMap1740_checked
#print axioms fusedMap1740_checked
#print axioms certified1740
def sourceMap1740swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1740swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1740swap_checked : acceptsGraphIso
    (source (graph core1740) (root 10) 2 0) DegreeTwoThreeSpectrum2603.graph sourceMap1740swap=true := by decide +kernel
theorem fusedMap1740swap_checked : acceptsGraphIso
    (fused (graph core1740) (root 10) 2 0) DegreeTwoThreeSpectrum2602.graph fusedMap1740swap=true := by decide +kernel
theorem certified1740swap : Certified (graph core1740) (root 10) 2 0 :=
  of_native_maps core1740 DegreeTwoThreeSpectrum2603.graph DegreeTwoThreeSpectrum2602.graph
    sourceMap1740swap fusedMap1740swap sourceMap1740swap_checked fusedMap1740swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1740
#print axioms sourceMap1740swap_checked
#print axioms fusedMap1740swap_checked
#print axioms certified1740swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
