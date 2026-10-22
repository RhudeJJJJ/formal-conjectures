/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1200 : Family 9 := level9.get ⟨48,by decide⟩
def sourceMap1200 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,13,9,10,11] (sourceLabel 9 0 2 v)
def fusedMap1200 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 0 2 v)
theorem sourceMap1200_checked : acceptsGraphIso
    (source (graph core1200) (root 9) 0 2) DegreeTwoThreeSpectrum1754.graph sourceMap1200=true := by decide +kernel
theorem fusedMap1200_checked : acceptsGraphIso
    (fused (graph core1200) (root 9) 0 2) DegreeTwoThreeSpectrum1756.graph fusedMap1200=true := by decide +kernel
theorem certified1200 : Certified (graph core1200) (root 9) 0 2 :=
  of_native_maps core1200 DegreeTwoThreeSpectrum1754.graph DegreeTwoThreeSpectrum1756.graph
    sourceMap1200 fusedMap1200 sourceMap1200_checked fusedMap1200_checked
    DegreeTwoThreeFiniteComparisons.comparison1200
#print axioms sourceMap1200_checked
#print axioms fusedMap1200_checked
#print axioms certified1200
def sourceMap1200swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11,13] (sourceLabel 9 2 0 v)
def fusedMap1200swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![8,0,1,2,3,4,5,6,7,13,9,10,11,12] (fusedLabel 9 2 0 v)
theorem sourceMap1200swap_checked : acceptsGraphIso
    (source (graph core1200) (root 9) 2 0) DegreeTwoThreeSpectrum1754.graph sourceMap1200swap=true := by decide +kernel
theorem fusedMap1200swap_checked : acceptsGraphIso
    (fused (graph core1200) (root 9) 2 0) DegreeTwoThreeSpectrum1756.graph fusedMap1200swap=true := by decide +kernel
theorem certified1200swap : Certified (graph core1200) (root 9) 2 0 :=
  of_native_maps core1200 DegreeTwoThreeSpectrum1754.graph DegreeTwoThreeSpectrum1756.graph
    sourceMap1200swap fusedMap1200swap sourceMap1200swap_checked fusedMap1200swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1200
#print axioms sourceMap1200swap_checked
#print axioms fusedMap1200swap_checked
#print axioms certified1200swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
