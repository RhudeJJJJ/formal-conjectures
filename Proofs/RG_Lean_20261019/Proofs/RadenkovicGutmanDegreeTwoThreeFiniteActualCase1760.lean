/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1760 : Family 10 := level10.get ⟨1029,by decide⟩
def sourceMap1760 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1760 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1760_checked : acceptsGraphIso
    (source (graph core1760) (root 10) 0 2) DegreeTwoThreeSpectrum3054.graph sourceMap1760=true := by decide +kernel
theorem fusedMap1760_checked : acceptsGraphIso
    (fused (graph core1760) (root 10) 0 2) DegreeTwoThreeSpectrum3058.graph fusedMap1760=true := by decide +kernel
theorem certified1760 : Certified (graph core1760) (root 10) 0 2 :=
  of_native_maps core1760 DegreeTwoThreeSpectrum3054.graph DegreeTwoThreeSpectrum3058.graph
    sourceMap1760 fusedMap1760 sourceMap1760_checked fusedMap1760_checked
    DegreeTwoThreeFiniteComparisons.comparison1760
#print axioms sourceMap1760_checked
#print axioms fusedMap1760_checked
#print axioms certified1760
def sourceMap1760swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1760swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1760swap_checked : acceptsGraphIso
    (source (graph core1760) (root 10) 2 0) DegreeTwoThreeSpectrum3054.graph sourceMap1760swap=true := by decide +kernel
theorem fusedMap1760swap_checked : acceptsGraphIso
    (fused (graph core1760) (root 10) 2 0) DegreeTwoThreeSpectrum3058.graph fusedMap1760swap=true := by decide +kernel
theorem certified1760swap : Certified (graph core1760) (root 10) 2 0 :=
  of_native_maps core1760 DegreeTwoThreeSpectrum3054.graph DegreeTwoThreeSpectrum3058.graph
    sourceMap1760swap fusedMap1760swap sourceMap1760swap_checked fusedMap1760swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1760
#print axioms sourceMap1760swap_checked
#print axioms fusedMap1760swap_checked
#print axioms certified1760swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
