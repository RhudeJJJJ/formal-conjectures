/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1895 : Family 10 := level10.get ⟨1363,by decide⟩
def sourceMap1895 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1895 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1895_checked : acceptsGraphIso
    (source (graph core1895) (root 10) 0 2) DegreeTwoThreeSpectrum3554.graph sourceMap1895=true := by decide +kernel
theorem fusedMap1895_checked : acceptsGraphIso
    (fused (graph core1895) (root 10) 0 2) DegreeTwoThreeSpectrum3555.graph fusedMap1895=true := by decide +kernel
theorem certified1895 : Certified (graph core1895) (root 10) 0 2 :=
  of_native_maps core1895 DegreeTwoThreeSpectrum3554.graph DegreeTwoThreeSpectrum3555.graph
    sourceMap1895 fusedMap1895 sourceMap1895_checked fusedMap1895_checked
    DegreeTwoThreeFiniteComparisons.comparison1895
#print axioms sourceMap1895_checked
#print axioms fusedMap1895_checked
#print axioms certified1895
def sourceMap1895swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1895swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1895swap_checked : acceptsGraphIso
    (source (graph core1895) (root 10) 2 0) DegreeTwoThreeSpectrum3554.graph sourceMap1895swap=true := by decide +kernel
theorem fusedMap1895swap_checked : acceptsGraphIso
    (fused (graph core1895) (root 10) 2 0) DegreeTwoThreeSpectrum3555.graph fusedMap1895swap=true := by decide +kernel
theorem certified1895swap : Certified (graph core1895) (root 10) 2 0 :=
  of_native_maps core1895 DegreeTwoThreeSpectrum3554.graph DegreeTwoThreeSpectrum3555.graph
    sourceMap1895swap fusedMap1895swap sourceMap1895swap_checked fusedMap1895swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1895
#print axioms sourceMap1895swap_checked
#print axioms fusedMap1895swap_checked
#print axioms certified1895swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
