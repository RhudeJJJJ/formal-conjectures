/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1964 : Family 10 := level10.get ⟨1538,by decide⟩
def sourceMap1964 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1964 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1964_checked : acceptsGraphIso
    (source (graph core1964) (root 10) 0 2) DegreeTwoThreeSpectrum3745.graph sourceMap1964=true := by decide +kernel
theorem fusedMap1964_checked : acceptsGraphIso
    (fused (graph core1964) (root 10) 0 2) DegreeTwoThreeSpectrum3012.graph fusedMap1964=true := by decide +kernel
theorem certified1964 : Certified (graph core1964) (root 10) 0 2 :=
  of_native_maps core1964 DegreeTwoThreeSpectrum3745.graph DegreeTwoThreeSpectrum3012.graph
    sourceMap1964 fusedMap1964 sourceMap1964_checked fusedMap1964_checked
    DegreeTwoThreeFiniteComparisons.comparison1964
#print axioms sourceMap1964_checked
#print axioms fusedMap1964_checked
#print axioms certified1964
def sourceMap1964swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1964swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1964swap_checked : acceptsGraphIso
    (source (graph core1964) (root 10) 2 0) DegreeTwoThreeSpectrum3745.graph sourceMap1964swap=true := by decide +kernel
theorem fusedMap1964swap_checked : acceptsGraphIso
    (fused (graph core1964) (root 10) 2 0) DegreeTwoThreeSpectrum3012.graph fusedMap1964swap=true := by decide +kernel
theorem certified1964swap : Certified (graph core1964) (root 10) 2 0 :=
  of_native_maps core1964 DegreeTwoThreeSpectrum3745.graph DegreeTwoThreeSpectrum3012.graph
    sourceMap1964swap fusedMap1964swap sourceMap1964swap_checked fusedMap1964swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1964
#print axioms sourceMap1964swap_checked
#print axioms fusedMap1964swap_checked
#print axioms certified1964swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
