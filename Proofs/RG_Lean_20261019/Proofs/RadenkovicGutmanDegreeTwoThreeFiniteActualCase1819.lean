/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1819 : Family 10 := level10.get ⟨1183,by decide⟩
def sourceMap1819 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1819 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1819_checked : acceptsGraphIso
    (source (graph core1819) (root 10) 0 2) DegreeTwoThreeSpectrum3296.graph sourceMap1819=true := by decide +kernel
theorem fusedMap1819_checked : acceptsGraphIso
    (fused (graph core1819) (root 10) 0 2) DegreeTwoThreeSpectrum3298.graph fusedMap1819=true := by decide +kernel
theorem certified1819 : Certified (graph core1819) (root 10) 0 2 :=
  of_native_maps core1819 DegreeTwoThreeSpectrum3296.graph DegreeTwoThreeSpectrum3298.graph
    sourceMap1819 fusedMap1819 sourceMap1819_checked fusedMap1819_checked
    DegreeTwoThreeFiniteComparisons.comparison1819
#print axioms sourceMap1819_checked
#print axioms fusedMap1819_checked
#print axioms certified1819
def sourceMap1819swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1819swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1819swap_checked : acceptsGraphIso
    (source (graph core1819) (root 10) 2 0) DegreeTwoThreeSpectrum3296.graph sourceMap1819swap=true := by decide +kernel
theorem fusedMap1819swap_checked : acceptsGraphIso
    (fused (graph core1819) (root 10) 2 0) DegreeTwoThreeSpectrum3298.graph fusedMap1819swap=true := by decide +kernel
theorem certified1819swap : Certified (graph core1819) (root 10) 2 0 :=
  of_native_maps core1819 DegreeTwoThreeSpectrum3296.graph DegreeTwoThreeSpectrum3298.graph
    sourceMap1819swap fusedMap1819swap sourceMap1819swap_checked fusedMap1819swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1819
#print axioms sourceMap1819swap_checked
#print axioms fusedMap1819swap_checked
#print axioms certified1819swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
