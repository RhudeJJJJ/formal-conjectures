/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1525 : Family 10 := level10.get ⟨375,by decide⟩
def sourceMap1525 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1525 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1525_checked : acceptsGraphIso
    (source (graph core1525) (root 10) 0 2) DegreeTwoThreeSpectrum2838.graph sourceMap1525=true := by decide +kernel
theorem fusedMap1525_checked : acceptsGraphIso
    (fused (graph core1525) (root 10) 0 2) DegreeTwoThreeSpectrum2840.graph fusedMap1525=true := by decide +kernel
theorem certified1525 : Certified (graph core1525) (root 10) 0 2 :=
  of_native_maps core1525 DegreeTwoThreeSpectrum2838.graph DegreeTwoThreeSpectrum2840.graph
    sourceMap1525 fusedMap1525 sourceMap1525_checked fusedMap1525_checked
    DegreeTwoThreeFiniteComparisons.comparison1525
#print axioms sourceMap1525_checked
#print axioms fusedMap1525_checked
#print axioms certified1525
def sourceMap1525swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1525swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1525swap_checked : acceptsGraphIso
    (source (graph core1525) (root 10) 2 0) DegreeTwoThreeSpectrum2838.graph sourceMap1525swap=true := by decide +kernel
theorem fusedMap1525swap_checked : acceptsGraphIso
    (fused (graph core1525) (root 10) 2 0) DegreeTwoThreeSpectrum2840.graph fusedMap1525swap=true := by decide +kernel
theorem certified1525swap : Certified (graph core1525) (root 10) 2 0 :=
  of_native_maps core1525 DegreeTwoThreeSpectrum2838.graph DegreeTwoThreeSpectrum2840.graph
    sourceMap1525swap fusedMap1525swap sourceMap1525swap_checked fusedMap1525swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1525
#print axioms sourceMap1525swap_checked
#print axioms fusedMap1525swap_checked
#print axioms certified1525swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
