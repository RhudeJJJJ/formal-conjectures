/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1205 : Family 9 := level9.get ⟨67,by decide⟩
def sourceMap1205 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1205 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1205_checked : acceptsGraphIso
    (source (graph core1205) (root 9) 0 2) DegreeTwoThreeSpectrum1796.graph sourceMap1205=true := by decide +kernel
theorem fusedMap1205_checked : acceptsGraphIso
    (fused (graph core1205) (root 9) 0 2) DegreeTwoThreeSpectrum1801.graph fusedMap1205=true := by decide +kernel
theorem certified1205 : Certified (graph core1205) (root 9) 0 2 :=
  of_native_maps core1205 DegreeTwoThreeSpectrum1796.graph DegreeTwoThreeSpectrum1801.graph
    sourceMap1205 fusedMap1205 sourceMap1205_checked fusedMap1205_checked
    DegreeTwoThreeFiniteComparisons.comparison1205
#print axioms sourceMap1205_checked
#print axioms fusedMap1205_checked
#print axioms certified1205
def sourceMap1205swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1205swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1205swap_checked : acceptsGraphIso
    (source (graph core1205) (root 9) 2 0) DegreeTwoThreeSpectrum1796.graph sourceMap1205swap=true := by decide +kernel
theorem fusedMap1205swap_checked : acceptsGraphIso
    (fused (graph core1205) (root 9) 2 0) DegreeTwoThreeSpectrum1801.graph fusedMap1205swap=true := by decide +kernel
theorem certified1205swap : Certified (graph core1205) (root 9) 2 0 :=
  of_native_maps core1205 DegreeTwoThreeSpectrum1796.graph DegreeTwoThreeSpectrum1801.graph
    sourceMap1205swap fusedMap1205swap sourceMap1205swap_checked fusedMap1205swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1205
#print axioms sourceMap1205swap_checked
#print axioms fusedMap1205swap_checked
#print axioms certified1205swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
