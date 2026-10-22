/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1929 : Family 10 := level10.get ⟨1442,by decide⟩
def sourceMap1929 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1929 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1929_checked : acceptsGraphIso
    (source (graph core1929) (root 10) 0 2) DegreeTwoThreeSpectrum3671.graph sourceMap1929=true := by decide +kernel
theorem fusedMap1929_checked : acceptsGraphIso
    (fused (graph core1929) (root 10) 0 2) DegreeTwoThreeSpectrum3672.graph fusedMap1929=true := by decide +kernel
theorem certified1929 : Certified (graph core1929) (root 10) 0 2 :=
  of_native_maps core1929 DegreeTwoThreeSpectrum3671.graph DegreeTwoThreeSpectrum3672.graph
    sourceMap1929 fusedMap1929 sourceMap1929_checked fusedMap1929_checked
    DegreeTwoThreeFiniteComparisons.comparison1929
#print axioms sourceMap1929_checked
#print axioms fusedMap1929_checked
#print axioms certified1929
def sourceMap1929swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1929swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1929swap_checked : acceptsGraphIso
    (source (graph core1929) (root 10) 2 0) DegreeTwoThreeSpectrum3671.graph sourceMap1929swap=true := by decide +kernel
theorem fusedMap1929swap_checked : acceptsGraphIso
    (fused (graph core1929) (root 10) 2 0) DegreeTwoThreeSpectrum3672.graph fusedMap1929swap=true := by decide +kernel
theorem certified1929swap : Certified (graph core1929) (root 10) 2 0 :=
  of_native_maps core1929 DegreeTwoThreeSpectrum3671.graph DegreeTwoThreeSpectrum3672.graph
    sourceMap1929swap fusedMap1929swap sourceMap1929swap_checked fusedMap1929swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1929
#print axioms sourceMap1929swap_checked
#print axioms fusedMap1929swap_checked
#print axioms certified1929swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
