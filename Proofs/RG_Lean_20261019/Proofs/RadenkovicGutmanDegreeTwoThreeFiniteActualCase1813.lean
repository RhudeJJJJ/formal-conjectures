/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1813 : Family 10 := level10.get ⟨1166,by decide⟩
def sourceMap1813 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1813 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1813_checked : acceptsGraphIso
    (source (graph core1813) (root 10) 0 2) DegreeTwoThreeSpectrum3277.graph sourceMap1813=true := by decide +kernel
theorem fusedMap1813_checked : acceptsGraphIso
    (fused (graph core1813) (root 10) 0 2) DegreeTwoThreeSpectrum3274.graph fusedMap1813=true := by decide +kernel
theorem certified1813 : Certified (graph core1813) (root 10) 0 2 :=
  of_native_maps core1813 DegreeTwoThreeSpectrum3277.graph DegreeTwoThreeSpectrum3274.graph
    sourceMap1813 fusedMap1813 sourceMap1813_checked fusedMap1813_checked
    DegreeTwoThreeFiniteComparisons.comparison1813
#print axioms sourceMap1813_checked
#print axioms fusedMap1813_checked
#print axioms certified1813
def sourceMap1813swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1813swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1813swap_checked : acceptsGraphIso
    (source (graph core1813) (root 10) 2 0) DegreeTwoThreeSpectrum3277.graph sourceMap1813swap=true := by decide +kernel
theorem fusedMap1813swap_checked : acceptsGraphIso
    (fused (graph core1813) (root 10) 2 0) DegreeTwoThreeSpectrum3274.graph fusedMap1813swap=true := by decide +kernel
theorem certified1813swap : Certified (graph core1813) (root 10) 2 0 :=
  of_native_maps core1813 DegreeTwoThreeSpectrum3277.graph DegreeTwoThreeSpectrum3274.graph
    sourceMap1813swap fusedMap1813swap sourceMap1813swap_checked fusedMap1813swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1813
#print axioms sourceMap1813swap_checked
#print axioms fusedMap1813swap_checked
#print axioms certified1813swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
