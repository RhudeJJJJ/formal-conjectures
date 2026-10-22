/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1601 : Family 10 := level10.get ⟨608,by decide⟩
def sourceMap1601 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,12,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1601 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1601_checked : acceptsGraphIso
    (source (graph core1601) (root 10) 0 2) DegreeTwoThreeSpectrum3273.graph sourceMap1601=true := by decide +kernel
theorem fusedMap1601_checked : acceptsGraphIso
    (fused (graph core1601) (root 10) 0 2) DegreeTwoThreeSpectrum2548.graph fusedMap1601=true := by decide +kernel
theorem certified1601 : Certified (graph core1601) (root 10) 0 2 :=
  of_native_maps core1601 DegreeTwoThreeSpectrum3273.graph DegreeTwoThreeSpectrum2548.graph
    sourceMap1601 fusedMap1601 sourceMap1601_checked fusedMap1601_checked
    DegreeTwoThreeFiniteComparisons.comparison1601
#print axioms sourceMap1601_checked
#print axioms fusedMap1601_checked
#print axioms certified1601
def sourceMap1601swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,11,8,9,10,12] (sourceLabel 10 2 0 v)
def fusedMap1601swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1601swap_checked : acceptsGraphIso
    (source (graph core1601) (root 10) 2 0) DegreeTwoThreeSpectrum3273.graph sourceMap1601swap=true := by decide +kernel
theorem fusedMap1601swap_checked : acceptsGraphIso
    (fused (graph core1601) (root 10) 2 0) DegreeTwoThreeSpectrum2548.graph fusedMap1601swap=true := by decide +kernel
theorem certified1601swap : Certified (graph core1601) (root 10) 2 0 :=
  of_native_maps core1601 DegreeTwoThreeSpectrum3273.graph DegreeTwoThreeSpectrum2548.graph
    sourceMap1601swap fusedMap1601swap sourceMap1601swap_checked fusedMap1601swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1601
#print axioms sourceMap1601swap_checked
#print axioms fusedMap1601swap_checked
#print axioms certified1601swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
