/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1831 : Family 10 := level10.get ⟨1208,by decide⟩
def sourceMap1831 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1831 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1831_checked : acceptsGraphIso
    (source (graph core1831) (root 10) 0 2) DegreeTwoThreeSpectrum3330.graph sourceMap1831=true := by decide +kernel
theorem fusedMap1831_checked : acceptsGraphIso
    (fused (graph core1831) (root 10) 0 2) DegreeTwoThreeSpectrum3334.graph fusedMap1831=true := by decide +kernel
theorem certified1831 : Certified (graph core1831) (root 10) 0 2 :=
  of_native_maps core1831 DegreeTwoThreeSpectrum3330.graph DegreeTwoThreeSpectrum3334.graph
    sourceMap1831 fusedMap1831 sourceMap1831_checked fusedMap1831_checked
    DegreeTwoThreeFiniteComparisons.comparison1831
#print axioms sourceMap1831_checked
#print axioms fusedMap1831_checked
#print axioms certified1831
def sourceMap1831swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1831swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1831swap_checked : acceptsGraphIso
    (source (graph core1831) (root 10) 2 0) DegreeTwoThreeSpectrum3330.graph sourceMap1831swap=true := by decide +kernel
theorem fusedMap1831swap_checked : acceptsGraphIso
    (fused (graph core1831) (root 10) 2 0) DegreeTwoThreeSpectrum3334.graph fusedMap1831swap=true := by decide +kernel
theorem certified1831swap : Certified (graph core1831) (root 10) 2 0 :=
  of_native_maps core1831 DegreeTwoThreeSpectrum3330.graph DegreeTwoThreeSpectrum3334.graph
    sourceMap1831swap fusedMap1831swap sourceMap1831swap_checked fusedMap1831swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1831
#print axioms sourceMap1831swap_checked
#print axioms fusedMap1831swap_checked
#print axioms certified1831swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
