/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1228 : Family 9 := level9.get ⟨150,by decide⟩
def sourceMap1228 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1228 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1228_checked : acceptsGraphIso
    (source (graph core1228) (root 9) 0 2) DegreeTwoThreeSpectrum1979.graph sourceMap1228=true := by decide +kernel
theorem fusedMap1228_checked : acceptsGraphIso
    (fused (graph core1228) (root 9) 0 2) DegreeTwoThreeSpectrum1749.graph fusedMap1228=true := by decide +kernel
theorem certified1228 : Certified (graph core1228) (root 9) 0 2 :=
  of_native_maps core1228 DegreeTwoThreeSpectrum1979.graph DegreeTwoThreeSpectrum1749.graph
    sourceMap1228 fusedMap1228 sourceMap1228_checked fusedMap1228_checked
    DegreeTwoThreeFiniteComparisons.comparison1228
#print axioms sourceMap1228_checked
#print axioms fusedMap1228_checked
#print axioms certified1228
def sourceMap1228swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1228swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1228swap_checked : acceptsGraphIso
    (source (graph core1228) (root 9) 2 0) DegreeTwoThreeSpectrum1979.graph sourceMap1228swap=true := by decide +kernel
theorem fusedMap1228swap_checked : acceptsGraphIso
    (fused (graph core1228) (root 9) 2 0) DegreeTwoThreeSpectrum1749.graph fusedMap1228swap=true := by decide +kernel
theorem certified1228swap : Certified (graph core1228) (root 9) 2 0 :=
  of_native_maps core1228 DegreeTwoThreeSpectrum1979.graph DegreeTwoThreeSpectrum1749.graph
    sourceMap1228swap fusedMap1228swap sourceMap1228swap_checked fusedMap1228swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1228
#print axioms sourceMap1228swap_checked
#print axioms fusedMap1228swap_checked
#print axioms certified1228swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
