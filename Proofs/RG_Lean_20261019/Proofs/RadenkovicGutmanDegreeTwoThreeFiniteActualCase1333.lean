/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1333 : Family 9 := level9.get ⟨440,by decide⟩
def sourceMap1333 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1333 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1333_checked : acceptsGraphIso
    (source (graph core1333) (root 9) 0 2) DegreeTwoThreeSpectrum2114.graph sourceMap1333=true := by decide +kernel
theorem fusedMap1333_checked : acceptsGraphIso
    (fused (graph core1333) (root 9) 0 2) DegreeTwoThreeSpectrum2115.graph fusedMap1333=true := by decide +kernel
theorem certified1333 : Certified (graph core1333) (root 9) 0 2 :=
  of_native_maps core1333 DegreeTwoThreeSpectrum2114.graph DegreeTwoThreeSpectrum2115.graph
    sourceMap1333 fusedMap1333 sourceMap1333_checked fusedMap1333_checked
    DegreeTwoThreeFiniteComparisons.comparison1333
#print axioms sourceMap1333_checked
#print axioms fusedMap1333_checked
#print axioms certified1333
def sourceMap1333swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1333swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1333swap_checked : acceptsGraphIso
    (source (graph core1333) (root 9) 2 0) DegreeTwoThreeSpectrum2114.graph sourceMap1333swap=true := by decide +kernel
theorem fusedMap1333swap_checked : acceptsGraphIso
    (fused (graph core1333) (root 9) 2 0) DegreeTwoThreeSpectrum2115.graph fusedMap1333swap=true := by decide +kernel
theorem certified1333swap : Certified (graph core1333) (root 9) 2 0 :=
  of_native_maps core1333 DegreeTwoThreeSpectrum2114.graph DegreeTwoThreeSpectrum2115.graph
    sourceMap1333swap fusedMap1333swap sourceMap1333swap_checked fusedMap1333swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1333
#print axioms sourceMap1333swap_checked
#print axioms fusedMap1333swap_checked
#print axioms certified1333swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
