/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1821 : Family 10 := level10.get ⟨1188,by decide⟩
def sourceMap1821 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1821 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1821_checked : acceptsGraphIso
    (source (graph core1821) (root 10) 0 2) DegreeTwoThreeSpectrum3304.graph sourceMap1821=true := by decide +kernel
theorem fusedMap1821_checked : acceptsGraphIso
    (fused (graph core1821) (root 10) 0 2) DegreeTwoThreeSpectrum3305.graph fusedMap1821=true := by decide +kernel
theorem certified1821 : Certified (graph core1821) (root 10) 0 2 :=
  of_native_maps core1821 DegreeTwoThreeSpectrum3304.graph DegreeTwoThreeSpectrum3305.graph
    sourceMap1821 fusedMap1821 sourceMap1821_checked fusedMap1821_checked
    DegreeTwoThreeFiniteComparisons.comparison1821
#print axioms sourceMap1821_checked
#print axioms fusedMap1821_checked
#print axioms certified1821
def sourceMap1821swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1821swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1821swap_checked : acceptsGraphIso
    (source (graph core1821) (root 10) 2 0) DegreeTwoThreeSpectrum3304.graph sourceMap1821swap=true := by decide +kernel
theorem fusedMap1821swap_checked : acceptsGraphIso
    (fused (graph core1821) (root 10) 2 0) DegreeTwoThreeSpectrum3305.graph fusedMap1821swap=true := by decide +kernel
theorem certified1821swap : Certified (graph core1821) (root 10) 2 0 :=
  of_native_maps core1821 DegreeTwoThreeSpectrum3304.graph DegreeTwoThreeSpectrum3305.graph
    sourceMap1821swap fusedMap1821swap sourceMap1821swap_checked fusedMap1821swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1821
#print axioms sourceMap1821swap_checked
#print axioms fusedMap1821swap_checked
#print axioms certified1821swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
