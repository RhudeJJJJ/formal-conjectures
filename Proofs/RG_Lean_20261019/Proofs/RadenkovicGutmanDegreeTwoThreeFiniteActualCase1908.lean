/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1908 : Family 10 := level10.get ⟨1388,by decide⟩
def sourceMap1908 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1908 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1908_checked : acceptsGraphIso
    (source (graph core1908) (root 10) 0 2) DegreeTwoThreeSpectrum3604.graph sourceMap1908=true := by decide +kernel
theorem fusedMap1908_checked : acceptsGraphIso
    (fused (graph core1908) (root 10) 0 2) DegreeTwoThreeSpectrum3603.graph fusedMap1908=true := by decide +kernel
theorem certified1908 : Certified (graph core1908) (root 10) 0 2 :=
  of_native_maps core1908 DegreeTwoThreeSpectrum3604.graph DegreeTwoThreeSpectrum3603.graph
    sourceMap1908 fusedMap1908 sourceMap1908_checked fusedMap1908_checked
    DegreeTwoThreeFiniteComparisons.comparison1908
#print axioms sourceMap1908_checked
#print axioms fusedMap1908_checked
#print axioms certified1908
def sourceMap1908swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1908swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1908swap_checked : acceptsGraphIso
    (source (graph core1908) (root 10) 2 0) DegreeTwoThreeSpectrum3604.graph sourceMap1908swap=true := by decide +kernel
theorem fusedMap1908swap_checked : acceptsGraphIso
    (fused (graph core1908) (root 10) 2 0) DegreeTwoThreeSpectrum3603.graph fusedMap1908swap=true := by decide +kernel
theorem certified1908swap : Certified (graph core1908) (root 10) 2 0 :=
  of_native_maps core1908 DegreeTwoThreeSpectrum3604.graph DegreeTwoThreeSpectrum3603.graph
    sourceMap1908swap fusedMap1908swap sourceMap1908swap_checked fusedMap1908swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1908
#print axioms sourceMap1908swap_checked
#print axioms fusedMap1908swap_checked
#print axioms certified1908swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
