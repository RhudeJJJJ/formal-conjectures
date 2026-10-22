/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1977 : Family 10 := level10.get ⟨1570,by decide⟩
def sourceMap1977 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1977 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1977_checked : acceptsGraphIso
    (source (graph core1977) (root 10) 0 2) DegreeTwoThreeSpectrum3761.graph sourceMap1977=true := by decide +kernel
theorem fusedMap1977_checked : acceptsGraphIso
    (fused (graph core1977) (root 10) 0 2) DegreeTwoThreeSpectrum3063.graph fusedMap1977=true := by decide +kernel
theorem certified1977 : Certified (graph core1977) (root 10) 0 2 :=
  of_native_maps core1977 DegreeTwoThreeSpectrum3761.graph DegreeTwoThreeSpectrum3063.graph
    sourceMap1977 fusedMap1977 sourceMap1977_checked fusedMap1977_checked
    DegreeTwoThreeFiniteComparisons.comparison1977
#print axioms sourceMap1977_checked
#print axioms fusedMap1977_checked
#print axioms certified1977
def sourceMap1977swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1977swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1977swap_checked : acceptsGraphIso
    (source (graph core1977) (root 10) 2 0) DegreeTwoThreeSpectrum3761.graph sourceMap1977swap=true := by decide +kernel
theorem fusedMap1977swap_checked : acceptsGraphIso
    (fused (graph core1977) (root 10) 2 0) DegreeTwoThreeSpectrum3063.graph fusedMap1977swap=true := by decide +kernel
theorem certified1977swap : Certified (graph core1977) (root 10) 2 0 :=
  of_native_maps core1977 DegreeTwoThreeSpectrum3761.graph DegreeTwoThreeSpectrum3063.graph
    sourceMap1977swap fusedMap1977swap sourceMap1977swap_checked fusedMap1977swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1977
#print axioms sourceMap1977swap_checked
#print axioms fusedMap1977swap_checked
#print axioms certified1977swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
