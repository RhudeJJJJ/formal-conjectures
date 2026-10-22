/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1595 : Family 10 := level10.get ⟨588,by decide⟩
def sourceMap1595 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1595 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1595_checked : acceptsGraphIso
    (source (graph core1595) (root 10) 0 2) DegreeTwoThreeSpectrum3231.graph sourceMap1595=true := by decide +kernel
theorem fusedMap1595_checked : acceptsGraphIso
    (fused (graph core1595) (root 10) 0 2) DegreeTwoThreeSpectrum2530.graph fusedMap1595=true := by decide +kernel
theorem certified1595 : Certified (graph core1595) (root 10) 0 2 :=
  of_native_maps core1595 DegreeTwoThreeSpectrum3231.graph DegreeTwoThreeSpectrum2530.graph
    sourceMap1595 fusedMap1595 sourceMap1595_checked fusedMap1595_checked
    DegreeTwoThreeFiniteComparisons.comparison1595
#print axioms sourceMap1595_checked
#print axioms fusedMap1595_checked
#print axioms certified1595
def sourceMap1595swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1595swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1595swap_checked : acceptsGraphIso
    (source (graph core1595) (root 10) 2 0) DegreeTwoThreeSpectrum3231.graph sourceMap1595swap=true := by decide +kernel
theorem fusedMap1595swap_checked : acceptsGraphIso
    (fused (graph core1595) (root 10) 2 0) DegreeTwoThreeSpectrum2530.graph fusedMap1595swap=true := by decide +kernel
theorem certified1595swap : Certified (graph core1595) (root 10) 2 0 :=
  of_native_maps core1595 DegreeTwoThreeSpectrum3231.graph DegreeTwoThreeSpectrum2530.graph
    sourceMap1595swap fusedMap1595swap sourceMap1595swap_checked fusedMap1595swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1595
#print axioms sourceMap1595swap_checked
#print axioms fusedMap1595swap_checked
#print axioms certified1595swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
