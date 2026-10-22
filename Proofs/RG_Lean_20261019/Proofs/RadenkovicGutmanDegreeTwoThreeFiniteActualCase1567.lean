/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1567 : Family 10 := level10.get ⟨492,by decide⟩
def sourceMap1567 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,5,6,7,8,9,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1567 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,6,7,8,9,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1567_checked : acceptsGraphIso
    (source (graph core1567) (root 10) 0 2) DegreeTwoThreeSpectrum2827.graph sourceMap1567=true := by decide +kernel
theorem fusedMap1567_checked : acceptsGraphIso
    (fused (graph core1567) (root 10) 0 2) DegreeTwoThreeSpectrum2964.graph fusedMap1567=true := by decide +kernel
theorem certified1567 : Certified (graph core1567) (root 10) 0 2 :=
  of_native_maps core1567 DegreeTwoThreeSpectrum2827.graph DegreeTwoThreeSpectrum2964.graph
    sourceMap1567 fusedMap1567 sourceMap1567_checked fusedMap1567_checked
    DegreeTwoThreeFiniteComparisons.comparison1567
#print axioms sourceMap1567_checked
#print axioms fusedMap1567_checked
#print axioms certified1567
def sourceMap1567swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,5,6,7,8,2,3,4,9] (sourceLabel 10 2 0 v)
def fusedMap1567swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,6,7,8,9,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1567swap_checked : acceptsGraphIso
    (source (graph core1567) (root 10) 2 0) DegreeTwoThreeSpectrum2827.graph sourceMap1567swap=true := by decide +kernel
theorem fusedMap1567swap_checked : acceptsGraphIso
    (fused (graph core1567) (root 10) 2 0) DegreeTwoThreeSpectrum2964.graph fusedMap1567swap=true := by decide +kernel
theorem certified1567swap : Certified (graph core1567) (root 10) 2 0 :=
  of_native_maps core1567 DegreeTwoThreeSpectrum2827.graph DegreeTwoThreeSpectrum2964.graph
    sourceMap1567swap fusedMap1567swap sourceMap1567swap_checked fusedMap1567swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1567
#print axioms sourceMap1567swap_checked
#print axioms fusedMap1567swap_checked
#print axioms certified1567swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
