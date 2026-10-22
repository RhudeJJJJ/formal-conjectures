/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1668 : Family 10 := level10.get ⟨796,by decide⟩
def sourceMap1668 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1668 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1668_checked : acceptsGraphIso
    (source (graph core1668) (root 10) 0 2) DegreeTwoThreeSpectrum3577.graph sourceMap1668=true := by decide +kernel
theorem fusedMap1668_checked : acceptsGraphIso
    (fused (graph core1668) (root 10) 0 2) DegreeTwoThreeSpectrum2766.graph fusedMap1668=true := by decide +kernel
theorem certified1668 : Certified (graph core1668) (root 10) 0 2 :=
  of_native_maps core1668 DegreeTwoThreeSpectrum3577.graph DegreeTwoThreeSpectrum2766.graph
    sourceMap1668 fusedMap1668 sourceMap1668_checked fusedMap1668_checked
    DegreeTwoThreeFiniteComparisons.comparison1668
#print axioms sourceMap1668_checked
#print axioms fusedMap1668_checked
#print axioms certified1668
def sourceMap1668swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1668swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1668swap_checked : acceptsGraphIso
    (source (graph core1668) (root 10) 2 0) DegreeTwoThreeSpectrum3577.graph sourceMap1668swap=true := by decide +kernel
theorem fusedMap1668swap_checked : acceptsGraphIso
    (fused (graph core1668) (root 10) 2 0) DegreeTwoThreeSpectrum2766.graph fusedMap1668swap=true := by decide +kernel
theorem certified1668swap : Certified (graph core1668) (root 10) 2 0 :=
  of_native_maps core1668 DegreeTwoThreeSpectrum3577.graph DegreeTwoThreeSpectrum2766.graph
    sourceMap1668swap fusedMap1668swap sourceMap1668swap_checked fusedMap1668swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1668
#print axioms sourceMap1668swap_checked
#print axioms fusedMap1668swap_checked
#print axioms certified1668swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
