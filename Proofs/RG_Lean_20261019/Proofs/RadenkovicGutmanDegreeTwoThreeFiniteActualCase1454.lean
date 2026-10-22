/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1454 : Family 10 := level10.get ⟨125,by decide⟩
def sourceMap1454 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1454 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1454_checked : acceptsGraphIso
    (source (graph core1454) (root 10) 0 2) DegreeTwoThreeSpectrum2866.graph sourceMap1454=true := by decide +kernel
theorem fusedMap1454_checked : acceptsGraphIso
    (fused (graph core1454) (root 10) 0 2) DegreeTwoThreeSpectrum2386.graph fusedMap1454=true := by decide +kernel
theorem certified1454 : Certified (graph core1454) (root 10) 0 2 :=
  of_native_maps core1454 DegreeTwoThreeSpectrum2866.graph DegreeTwoThreeSpectrum2386.graph
    sourceMap1454 fusedMap1454 sourceMap1454_checked fusedMap1454_checked
    DegreeTwoThreeFiniteComparisons.comparison1454
#print axioms sourceMap1454_checked
#print axioms fusedMap1454_checked
#print axioms certified1454
def sourceMap1454swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1454swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1454swap_checked : acceptsGraphIso
    (source (graph core1454) (root 10) 2 0) DegreeTwoThreeSpectrum2866.graph sourceMap1454swap=true := by decide +kernel
theorem fusedMap1454swap_checked : acceptsGraphIso
    (fused (graph core1454) (root 10) 2 0) DegreeTwoThreeSpectrum2386.graph fusedMap1454swap=true := by decide +kernel
theorem certified1454swap : Certified (graph core1454) (root 10) 2 0 :=
  of_native_maps core1454 DegreeTwoThreeSpectrum2866.graph DegreeTwoThreeSpectrum2386.graph
    sourceMap1454swap fusedMap1454swap sourceMap1454swap_checked fusedMap1454swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1454
#print axioms sourceMap1454swap_checked
#print axioms fusedMap1454swap_checked
#print axioms certified1454swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
