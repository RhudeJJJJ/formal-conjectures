/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1664 : Family 10 := level10.get ⟨786,by decide⟩
def sourceMap1664 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1664 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1664_checked : acceptsGraphIso
    (source (graph core1664) (root 10) 0 2) DegreeTwoThreeSpectrum3572.graph sourceMap1664=true := by decide +kernel
theorem fusedMap1664_checked : acceptsGraphIso
    (fused (graph core1664) (root 10) 0 2) DegreeTwoThreeSpectrum2753.graph fusedMap1664=true := by decide +kernel
theorem certified1664 : Certified (graph core1664) (root 10) 0 2 :=
  of_native_maps core1664 DegreeTwoThreeSpectrum3572.graph DegreeTwoThreeSpectrum2753.graph
    sourceMap1664 fusedMap1664 sourceMap1664_checked fusedMap1664_checked
    DegreeTwoThreeFiniteComparisons.comparison1664
#print axioms sourceMap1664_checked
#print axioms fusedMap1664_checked
#print axioms certified1664
def sourceMap1664swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1664swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1664swap_checked : acceptsGraphIso
    (source (graph core1664) (root 10) 2 0) DegreeTwoThreeSpectrum3572.graph sourceMap1664swap=true := by decide +kernel
theorem fusedMap1664swap_checked : acceptsGraphIso
    (fused (graph core1664) (root 10) 2 0) DegreeTwoThreeSpectrum2753.graph fusedMap1664swap=true := by decide +kernel
theorem certified1664swap : Certified (graph core1664) (root 10) 2 0 :=
  of_native_maps core1664 DegreeTwoThreeSpectrum3572.graph DegreeTwoThreeSpectrum2753.graph
    sourceMap1664swap fusedMap1664swap sourceMap1664swap_checked fusedMap1664swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1664
#print axioms sourceMap1664swap_checked
#print axioms fusedMap1664swap_checked
#print axioms certified1664swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
