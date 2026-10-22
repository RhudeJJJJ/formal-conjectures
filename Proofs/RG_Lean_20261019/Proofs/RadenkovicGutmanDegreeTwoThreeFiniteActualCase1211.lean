/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1211 : Family 9 := level9.get ⟨91,by decide⟩
def sourceMap1211 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,13,8,9,10] (sourceLabel 9 0 2 v)
def fusedMap1211 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 0 2 v)
theorem sourceMap1211_checked : acceptsGraphIso
    (source (graph core1211) (root 9) 0 2) DegreeTwoThreeSpectrum1851.graph sourceMap1211=true := by decide +kernel
theorem fusedMap1211_checked : acceptsGraphIso
    (fused (graph core1211) (root 9) 0 2) DegreeTwoThreeSpectrum1856.graph fusedMap1211=true := by decide +kernel
theorem certified1211 : Certified (graph core1211) (root 9) 0 2 :=
  of_native_maps core1211 DegreeTwoThreeSpectrum1851.graph DegreeTwoThreeSpectrum1856.graph
    sourceMap1211 fusedMap1211 sourceMap1211_checked fusedMap1211_checked
    DegreeTwoThreeFiniteComparisons.comparison1211
#print axioms sourceMap1211_checked
#print axioms fusedMap1211_checked
#print axioms certified1211
def sourceMap1211swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,8,9,10,13] (sourceLabel 9 2 0 v)
def fusedMap1211swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,12,13,8,9,10,11] (fusedLabel 9 2 0 v)
theorem sourceMap1211swap_checked : acceptsGraphIso
    (source (graph core1211) (root 9) 2 0) DegreeTwoThreeSpectrum1851.graph sourceMap1211swap=true := by decide +kernel
theorem fusedMap1211swap_checked : acceptsGraphIso
    (fused (graph core1211) (root 9) 2 0) DegreeTwoThreeSpectrum1856.graph fusedMap1211swap=true := by decide +kernel
theorem certified1211swap : Certified (graph core1211) (root 9) 2 0 :=
  of_native_maps core1211 DegreeTwoThreeSpectrum1851.graph DegreeTwoThreeSpectrum1856.graph
    sourceMap1211swap fusedMap1211swap sourceMap1211swap_checked fusedMap1211swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1211
#print axioms sourceMap1211swap_checked
#print axioms fusedMap1211swap_checked
#print axioms certified1211swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
