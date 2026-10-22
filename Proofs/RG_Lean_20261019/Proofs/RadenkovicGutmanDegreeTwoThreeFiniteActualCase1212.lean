/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1212 : Family 9 := level9.get ⟨98,by decide⟩
def sourceMap1212 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1212 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1212_checked : acceptsGraphIso
    (source (graph core1212) (root 9) 0 2) DegreeTwoThreeSpectrum1874.graph sourceMap1212=true := by decide +kernel
theorem fusedMap1212_checked : acceptsGraphIso
    (fused (graph core1212) (root 9) 0 2) DegreeTwoThreeSpectrum1876.graph fusedMap1212=true := by decide +kernel
theorem certified1212 : Certified (graph core1212) (root 9) 0 2 :=
  of_native_maps core1212 DegreeTwoThreeSpectrum1874.graph DegreeTwoThreeSpectrum1876.graph
    sourceMap1212 fusedMap1212 sourceMap1212_checked fusedMap1212_checked
    DegreeTwoThreeFiniteComparisons.comparison1212
#print axioms sourceMap1212_checked
#print axioms fusedMap1212_checked
#print axioms certified1212
def sourceMap1212swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1212swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1212swap_checked : acceptsGraphIso
    (source (graph core1212) (root 9) 2 0) DegreeTwoThreeSpectrum1874.graph sourceMap1212swap=true := by decide +kernel
theorem fusedMap1212swap_checked : acceptsGraphIso
    (fused (graph core1212) (root 9) 2 0) DegreeTwoThreeSpectrum1876.graph fusedMap1212swap=true := by decide +kernel
theorem certified1212swap : Certified (graph core1212) (root 9) 2 0 :=
  of_native_maps core1212 DegreeTwoThreeSpectrum1874.graph DegreeTwoThreeSpectrum1876.graph
    sourceMap1212swap fusedMap1212swap sourceMap1212swap_checked fusedMap1212swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1212
#print axioms sourceMap1212swap_checked
#print axioms fusedMap1212swap_checked
#print axioms certified1212swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
