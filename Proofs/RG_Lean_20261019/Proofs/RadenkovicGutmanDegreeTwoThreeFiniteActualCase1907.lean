/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1907 : Family 10 := level10.get ⟨1387,by decide⟩
def sourceMap1907 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1907 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1907_checked : acceptsGraphIso
    (source (graph core1907) (root 10) 0 2) DegreeTwoThreeSpectrum3589.graph sourceMap1907=true := by decide +kernel
theorem fusedMap1907_checked : acceptsGraphIso
    (fused (graph core1907) (root 10) 0 2) DegreeTwoThreeSpectrum3588.graph fusedMap1907=true := by decide +kernel
theorem certified1907 : Certified (graph core1907) (root 10) 0 2 :=
  of_native_maps core1907 DegreeTwoThreeSpectrum3589.graph DegreeTwoThreeSpectrum3588.graph
    sourceMap1907 fusedMap1907 sourceMap1907_checked fusedMap1907_checked
    DegreeTwoThreeFiniteComparisons.comparison1907
#print axioms sourceMap1907_checked
#print axioms fusedMap1907_checked
#print axioms certified1907
def sourceMap1907swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1907swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1907swap_checked : acceptsGraphIso
    (source (graph core1907) (root 10) 2 0) DegreeTwoThreeSpectrum3589.graph sourceMap1907swap=true := by decide +kernel
theorem fusedMap1907swap_checked : acceptsGraphIso
    (fused (graph core1907) (root 10) 2 0) DegreeTwoThreeSpectrum3588.graph fusedMap1907swap=true := by decide +kernel
theorem certified1907swap : Certified (graph core1907) (root 10) 2 0 :=
  of_native_maps core1907 DegreeTwoThreeSpectrum3589.graph DegreeTwoThreeSpectrum3588.graph
    sourceMap1907swap fusedMap1907swap sourceMap1907swap_checked fusedMap1907swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1907
#print axioms sourceMap1907swap_checked
#print axioms fusedMap1907swap_checked
#print axioms certified1907swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
