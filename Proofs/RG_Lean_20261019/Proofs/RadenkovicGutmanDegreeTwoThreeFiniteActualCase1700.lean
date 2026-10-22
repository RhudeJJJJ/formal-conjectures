/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1700 : Family 10 := level10.get ⟨881,by decide⟩
def sourceMap1700 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,7,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1700 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1700_checked : acceptsGraphIso
    (source (graph core1700) (root 10) 0 2) DegreeTwoThreeSpectrum3679.graph sourceMap1700=true := by decide +kernel
theorem fusedMap1700_checked : acceptsGraphIso
    (fused (graph core1700) (root 10) 0 2) DegreeTwoThreeSpectrum2877.graph fusedMap1700=true := by decide +kernel
theorem certified1700 : Certified (graph core1700) (root 10) 0 2 :=
  of_native_maps core1700 DegreeTwoThreeSpectrum3679.graph DegreeTwoThreeSpectrum2877.graph
    sourceMap1700 fusedMap1700 sourceMap1700_checked fusedMap1700_checked
    DegreeTwoThreeFiniteComparisons.comparison1700
#print axioms sourceMap1700_checked
#print axioms fusedMap1700_checked
#print axioms certified1700
def sourceMap1700swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,5,6,2,3,4,7] (sourceLabel 10 2 0 v)
def fusedMap1700swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1700swap_checked : acceptsGraphIso
    (source (graph core1700) (root 10) 2 0) DegreeTwoThreeSpectrum3679.graph sourceMap1700swap=true := by decide +kernel
theorem fusedMap1700swap_checked : acceptsGraphIso
    (fused (graph core1700) (root 10) 2 0) DegreeTwoThreeSpectrum2877.graph fusedMap1700swap=true := by decide +kernel
theorem certified1700swap : Certified (graph core1700) (root 10) 2 0 :=
  of_native_maps core1700 DegreeTwoThreeSpectrum3679.graph DegreeTwoThreeSpectrum2877.graph
    sourceMap1700swap fusedMap1700swap sourceMap1700swap_checked fusedMap1700swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1700
#print axioms sourceMap1700swap_checked
#print axioms fusedMap1700swap_checked
#print axioms certified1700swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
