/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1562 : Family 10 := level10.get ⟨484,by decide⟩
def sourceMap1562 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,9,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1562 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,6,7,8,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1562_checked : acceptsGraphIso
    (source (graph core1562) (root 10) 0 2) DegreeTwoThreeSpectrum2816.graph sourceMap1562=true := by decide +kernel
theorem fusedMap1562_checked : acceptsGraphIso
    (fused (graph core1562) (root 10) 0 2) DegreeTwoThreeSpectrum2960.graph fusedMap1562=true := by decide +kernel
theorem certified1562 : Certified (graph core1562) (root 10) 0 2 :=
  of_native_maps core1562 DegreeTwoThreeSpectrum2816.graph DegreeTwoThreeSpectrum2960.graph
    sourceMap1562 fusedMap1562 sourceMap1562_checked fusedMap1562_checked
    DegreeTwoThreeFiniteComparisons.comparison1562
#print axioms sourceMap1562_checked
#print axioms fusedMap1562_checked
#print axioms certified1562
def sourceMap1562swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,9,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1562swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,6,7,8,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1562swap_checked : acceptsGraphIso
    (source (graph core1562) (root 10) 2 0) DegreeTwoThreeSpectrum2816.graph sourceMap1562swap=true := by decide +kernel
theorem fusedMap1562swap_checked : acceptsGraphIso
    (fused (graph core1562) (root 10) 2 0) DegreeTwoThreeSpectrum2960.graph fusedMap1562swap=true := by decide +kernel
theorem certified1562swap : Certified (graph core1562) (root 10) 2 0 :=
  of_native_maps core1562 DegreeTwoThreeSpectrum2816.graph DegreeTwoThreeSpectrum2960.graph
    sourceMap1562swap fusedMap1562swap sourceMap1562swap_checked fusedMap1562swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1562
#print axioms sourceMap1562swap_checked
#print axioms fusedMap1562swap_checked
#print axioms certified1562swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
