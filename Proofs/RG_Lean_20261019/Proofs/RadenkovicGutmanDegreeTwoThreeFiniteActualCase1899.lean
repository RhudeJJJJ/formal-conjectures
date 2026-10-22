/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1899 : Family 10 := level10.get ⟨1371,by decide⟩
def sourceMap1899 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1899 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1899_checked : acceptsGraphIso
    (source (graph core1899) (root 10) 0 2) DegreeTwoThreeSpectrum3565.graph sourceMap1899=true := by decide +kernel
theorem fusedMap1899_checked : acceptsGraphIso
    (fused (graph core1899) (root 10) 0 2) DegreeTwoThreeSpectrum3566.graph fusedMap1899=true := by decide +kernel
theorem certified1899 : Certified (graph core1899) (root 10) 0 2 :=
  of_native_maps core1899 DegreeTwoThreeSpectrum3565.graph DegreeTwoThreeSpectrum3566.graph
    sourceMap1899 fusedMap1899 sourceMap1899_checked fusedMap1899_checked
    DegreeTwoThreeFiniteComparisons.comparison1899
#print axioms sourceMap1899_checked
#print axioms fusedMap1899_checked
#print axioms certified1899
def sourceMap1899swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1899swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1899swap_checked : acceptsGraphIso
    (source (graph core1899) (root 10) 2 0) DegreeTwoThreeSpectrum3565.graph sourceMap1899swap=true := by decide +kernel
theorem fusedMap1899swap_checked : acceptsGraphIso
    (fused (graph core1899) (root 10) 2 0) DegreeTwoThreeSpectrum3566.graph fusedMap1899swap=true := by decide +kernel
theorem certified1899swap : Certified (graph core1899) (root 10) 2 0 :=
  of_native_maps core1899 DegreeTwoThreeSpectrum3565.graph DegreeTwoThreeSpectrum3566.graph
    sourceMap1899swap fusedMap1899swap sourceMap1899swap_checked fusedMap1899swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1899
#print axioms sourceMap1899swap_checked
#print axioms fusedMap1899swap_checked
#print axioms certified1899swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
