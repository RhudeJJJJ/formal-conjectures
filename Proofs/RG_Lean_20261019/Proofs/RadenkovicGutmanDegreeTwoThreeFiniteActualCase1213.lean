/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1213 : Family 9 := level9.get ⟨102,by decide⟩
def sourceMap1213 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,6,2,3,4] (sourceLabel 9 0 2 v)
def fusedMap1213 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1213_checked : acceptsGraphIso
    (source (graph core1213) (root 9) 0 2) DegreeTwoThreeSpectrum1883.graph sourceMap1213=true := by decide +kernel
theorem fusedMap1213_checked : acceptsGraphIso
    (fused (graph core1213) (root 9) 0 2) DegreeTwoThreeSpectrum1888.graph fusedMap1213=true := by decide +kernel
theorem certified1213 : Certified (graph core1213) (root 9) 0 2 :=
  of_native_maps core1213 DegreeTwoThreeSpectrum1883.graph DegreeTwoThreeSpectrum1888.graph
    sourceMap1213 fusedMap1213 sourceMap1213_checked fusedMap1213_checked
    DegreeTwoThreeFiniteComparisons.comparison1213
#print axioms sourceMap1213_checked
#print axioms fusedMap1213_checked
#print axioms certified1213
def sourceMap1213swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,0,7,8,9,10,11,12,13,5,2,3,4,6] (sourceLabel 9 2 0 v)
def fusedMap1213swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1213swap_checked : acceptsGraphIso
    (source (graph core1213) (root 9) 2 0) DegreeTwoThreeSpectrum1883.graph sourceMap1213swap=true := by decide +kernel
theorem fusedMap1213swap_checked : acceptsGraphIso
    (fused (graph core1213) (root 9) 2 0) DegreeTwoThreeSpectrum1888.graph fusedMap1213swap=true := by decide +kernel
theorem certified1213swap : Certified (graph core1213) (root 9) 2 0 :=
  of_native_maps core1213 DegreeTwoThreeSpectrum1883.graph DegreeTwoThreeSpectrum1888.graph
    sourceMap1213swap fusedMap1213swap sourceMap1213swap_checked fusedMap1213swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1213
#print axioms sourceMap1213swap_checked
#print axioms fusedMap1213swap_checked
#print axioms certified1213swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
