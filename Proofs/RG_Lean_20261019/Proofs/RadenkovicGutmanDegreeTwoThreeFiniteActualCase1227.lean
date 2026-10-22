/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1227 : Family 9 := level9.get ⟨146,by decide⟩
def sourceMap1227 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1227 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1227_checked : acceptsGraphIso
    (source (graph core1227) (root 9) 0 2) DegreeTwoThreeSpectrum1967.graph sourceMap1227=true := by decide +kernel
theorem fusedMap1227_checked : acceptsGraphIso
    (fused (graph core1227) (root 9) 0 2) DegreeTwoThreeSpectrum1745.graph fusedMap1227=true := by decide +kernel
theorem certified1227 : Certified (graph core1227) (root 9) 0 2 :=
  of_native_maps core1227 DegreeTwoThreeSpectrum1967.graph DegreeTwoThreeSpectrum1745.graph
    sourceMap1227 fusedMap1227 sourceMap1227_checked fusedMap1227_checked
    DegreeTwoThreeFiniteComparisons.comparison1227
#print axioms sourceMap1227_checked
#print axioms fusedMap1227_checked
#print axioms certified1227
def sourceMap1227swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1227swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1227swap_checked : acceptsGraphIso
    (source (graph core1227) (root 9) 2 0) DegreeTwoThreeSpectrum1967.graph sourceMap1227swap=true := by decide +kernel
theorem fusedMap1227swap_checked : acceptsGraphIso
    (fused (graph core1227) (root 9) 2 0) DegreeTwoThreeSpectrum1745.graph fusedMap1227swap=true := by decide +kernel
theorem certified1227swap : Certified (graph core1227) (root 9) 2 0 :=
  of_native_maps core1227 DegreeTwoThreeSpectrum1967.graph DegreeTwoThreeSpectrum1745.graph
    sourceMap1227swap fusedMap1227swap sourceMap1227swap_checked fusedMap1227swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1227
#print axioms sourceMap1227swap_checked
#print axioms fusedMap1227swap_checked
#print axioms certified1227swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
