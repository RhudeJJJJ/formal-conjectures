/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1681 : Family 10 := level10.get ⟨825,by decide⟩
def sourceMap1681 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,14,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1681 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1681_checked : acceptsGraphIso
    (source (graph core1681) (root 10) 0 2) DegreeTwoThreeSpectrum3595.graph sourceMap1681=true := by decide +kernel
theorem fusedMap1681_checked : acceptsGraphIso
    (fused (graph core1681) (root 10) 0 2) DegreeTwoThreeSpectrum2809.graph fusedMap1681=true := by decide +kernel
theorem certified1681 : Certified (graph core1681) (root 10) 0 2 :=
  of_native_maps core1681 DegreeTwoThreeSpectrum3595.graph DegreeTwoThreeSpectrum2809.graph
    sourceMap1681 fusedMap1681 sourceMap1681_checked fusedMap1681_checked
    DegreeTwoThreeFiniteComparisons.comparison1681
#print axioms sourceMap1681_checked
#print axioms fusedMap1681_checked
#print axioms certified1681
def sourceMap1681swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9,14] (sourceLabel 10 2 0 v)
def fusedMap1681swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1681swap_checked : acceptsGraphIso
    (source (graph core1681) (root 10) 2 0) DegreeTwoThreeSpectrum3595.graph sourceMap1681swap=true := by decide +kernel
theorem fusedMap1681swap_checked : acceptsGraphIso
    (fused (graph core1681) (root 10) 2 0) DegreeTwoThreeSpectrum2809.graph fusedMap1681swap=true := by decide +kernel
theorem certified1681swap : Certified (graph core1681) (root 10) 2 0 :=
  of_native_maps core1681 DegreeTwoThreeSpectrum3595.graph DegreeTwoThreeSpectrum2809.graph
    sourceMap1681swap fusedMap1681swap sourceMap1681swap_checked fusedMap1681swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1681
#print axioms sourceMap1681swap_checked
#print axioms fusedMap1681swap_checked
#print axioms certified1681swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
