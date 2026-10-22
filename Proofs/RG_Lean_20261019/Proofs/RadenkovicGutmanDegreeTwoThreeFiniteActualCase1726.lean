/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1726 : Family 10 := level10.get ⟨949,by decide⟩
def sourceMap1726 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1726 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1726_checked : acceptsGraphIso
    (source (graph core1726) (root 10) 0 2) DegreeTwoThreeSpectrum3713.graph sourceMap1726=true := by decide +kernel
theorem fusedMap1726_checked : acceptsGraphIso
    (fused (graph core1726) (root 10) 0 2) DegreeTwoThreeSpectrum2972.graph fusedMap1726=true := by decide +kernel
theorem certified1726 : Certified (graph core1726) (root 10) 0 2 :=
  of_native_maps core1726 DegreeTwoThreeSpectrum3713.graph DegreeTwoThreeSpectrum2972.graph
    sourceMap1726 fusedMap1726 sourceMap1726_checked fusedMap1726_checked
    DegreeTwoThreeFiniteComparisons.comparison1726
#print axioms sourceMap1726_checked
#print axioms fusedMap1726_checked
#print axioms certified1726
def sourceMap1726swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1726swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1726swap_checked : acceptsGraphIso
    (source (graph core1726) (root 10) 2 0) DegreeTwoThreeSpectrum3713.graph sourceMap1726swap=true := by decide +kernel
theorem fusedMap1726swap_checked : acceptsGraphIso
    (fused (graph core1726) (root 10) 2 0) DegreeTwoThreeSpectrum2972.graph fusedMap1726swap=true := by decide +kernel
theorem certified1726swap : Certified (graph core1726) (root 10) 2 0 :=
  of_native_maps core1726 DegreeTwoThreeSpectrum3713.graph DegreeTwoThreeSpectrum2972.graph
    sourceMap1726swap fusedMap1726swap sourceMap1726swap_checked fusedMap1726swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1726
#print axioms sourceMap1726swap_checked
#print axioms fusedMap1726swap_checked
#print axioms certified1726swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
