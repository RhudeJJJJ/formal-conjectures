/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1847 : Family 10 := level10.get ⟨1247,by decide⟩
def sourceMap1847 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1847 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1847_checked : acceptsGraphIso
    (source (graph core1847) (root 10) 0 2) DegreeTwoThreeSpectrum3386.graph sourceMap1847=true := by decide +kernel
theorem fusedMap1847_checked : acceptsGraphIso
    (fused (graph core1847) (root 10) 0 2) DegreeTwoThreeSpectrum3388.graph fusedMap1847=true := by decide +kernel
theorem certified1847 : Certified (graph core1847) (root 10) 0 2 :=
  of_native_maps core1847 DegreeTwoThreeSpectrum3386.graph DegreeTwoThreeSpectrum3388.graph
    sourceMap1847 fusedMap1847 sourceMap1847_checked fusedMap1847_checked
    DegreeTwoThreeFiniteComparisons.comparison1847
#print axioms sourceMap1847_checked
#print axioms fusedMap1847_checked
#print axioms certified1847
def sourceMap1847swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1847swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1847swap_checked : acceptsGraphIso
    (source (graph core1847) (root 10) 2 0) DegreeTwoThreeSpectrum3386.graph sourceMap1847swap=true := by decide +kernel
theorem fusedMap1847swap_checked : acceptsGraphIso
    (fused (graph core1847) (root 10) 2 0) DegreeTwoThreeSpectrum3388.graph fusedMap1847swap=true := by decide +kernel
theorem certified1847swap : Certified (graph core1847) (root 10) 2 0 :=
  of_native_maps core1847 DegreeTwoThreeSpectrum3386.graph DegreeTwoThreeSpectrum3388.graph
    sourceMap1847swap fusedMap1847swap sourceMap1847swap_checked fusedMap1847swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1847
#print axioms sourceMap1847swap_checked
#print axioms fusedMap1847swap_checked
#print axioms certified1847swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
