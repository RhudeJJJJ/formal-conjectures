/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1919 : Family 10 := level10.get ⟨1419,by decide⟩
def sourceMap1919 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1919 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1919_checked : acceptsGraphIso
    (source (graph core1919) (root 10) 0 2) DegreeTwoThreeSpectrum3639.graph sourceMap1919=true := by decide +kernel
theorem fusedMap1919_checked : acceptsGraphIso
    (fused (graph core1919) (root 10) 0 2) DegreeTwoThreeSpectrum3640.graph fusedMap1919=true := by decide +kernel
theorem certified1919 : Certified (graph core1919) (root 10) 0 2 :=
  of_native_maps core1919 DegreeTwoThreeSpectrum3639.graph DegreeTwoThreeSpectrum3640.graph
    sourceMap1919 fusedMap1919 sourceMap1919_checked fusedMap1919_checked
    DegreeTwoThreeFiniteComparisons.comparison1919
#print axioms sourceMap1919_checked
#print axioms fusedMap1919_checked
#print axioms certified1919
def sourceMap1919swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1919swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1919swap_checked : acceptsGraphIso
    (source (graph core1919) (root 10) 2 0) DegreeTwoThreeSpectrum3639.graph sourceMap1919swap=true := by decide +kernel
theorem fusedMap1919swap_checked : acceptsGraphIso
    (fused (graph core1919) (root 10) 2 0) DegreeTwoThreeSpectrum3640.graph fusedMap1919swap=true := by decide +kernel
theorem certified1919swap : Certified (graph core1919) (root 10) 2 0 :=
  of_native_maps core1919 DegreeTwoThreeSpectrum3639.graph DegreeTwoThreeSpectrum3640.graph
    sourceMap1919swap fusedMap1919swap sourceMap1919swap_checked fusedMap1919swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1919
#print axioms sourceMap1919swap_checked
#print axioms fusedMap1919swap_checked
#print axioms certified1919swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
