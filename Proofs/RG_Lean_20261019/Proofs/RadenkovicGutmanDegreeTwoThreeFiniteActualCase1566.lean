/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1566 : Family 10 := level10.get ⟨490,by decide⟩
def sourceMap1566 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1566 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,6,7,8,9,2,3,4,5] (fusedLabel 10 0 2 v)
theorem sourceMap1566_checked : acceptsGraphIso
    (source (graph core1566) (root 10) 0 2) DegreeTwoThreeSpectrum2732.graph sourceMap1566=true := by decide +kernel
theorem fusedMap1566_checked : acceptsGraphIso
    (fused (graph core1566) (root 10) 0 2) DegreeTwoThreeSpectrum2953.graph fusedMap1566=true := by decide +kernel
theorem certified1566 : Certified (graph core1566) (root 10) 0 2 :=
  of_native_maps core1566 DegreeTwoThreeSpectrum2732.graph DegreeTwoThreeSpectrum2953.graph
    sourceMap1566 fusedMap1566 sourceMap1566_checked fusedMap1566_checked
    DegreeTwoThreeFiniteComparisons.comparison1566
#print axioms sourceMap1566_checked
#print axioms fusedMap1566_checked
#print axioms certified1566
def sourceMap1566swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1566swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,6,7,8,9,2,3,4,5] (fusedLabel 10 2 0 v)
theorem sourceMap1566swap_checked : acceptsGraphIso
    (source (graph core1566) (root 10) 2 0) DegreeTwoThreeSpectrum2732.graph sourceMap1566swap=true := by decide +kernel
theorem fusedMap1566swap_checked : acceptsGraphIso
    (fused (graph core1566) (root 10) 2 0) DegreeTwoThreeSpectrum2953.graph fusedMap1566swap=true := by decide +kernel
theorem certified1566swap : Certified (graph core1566) (root 10) 2 0 :=
  of_native_maps core1566 DegreeTwoThreeSpectrum2732.graph DegreeTwoThreeSpectrum2953.graph
    sourceMap1566swap fusedMap1566swap sourceMap1566swap_checked fusedMap1566swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1566
#print axioms sourceMap1566swap_checked
#print axioms fusedMap1566swap_checked
#print axioms certified1566swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
