/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1969 : Family 10 := level10.get ⟨1551,by decide⟩
def sourceMap1969 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1969 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1969_checked : acceptsGraphIso
    (source (graph core1969) (root 10) 0 2) DegreeTwoThreeSpectrum3752.graph sourceMap1969=true := by decide +kernel
theorem fusedMap1969_checked : acceptsGraphIso
    (fused (graph core1969) (root 10) 0 2) DegreeTwoThreeSpectrum3029.graph fusedMap1969=true := by decide +kernel
theorem certified1969 : Certified (graph core1969) (root 10) 0 2 :=
  of_native_maps core1969 DegreeTwoThreeSpectrum3752.graph DegreeTwoThreeSpectrum3029.graph
    sourceMap1969 fusedMap1969 sourceMap1969_checked fusedMap1969_checked
    DegreeTwoThreeFiniteComparisons.comparison1969
#print axioms sourceMap1969_checked
#print axioms fusedMap1969_checked
#print axioms certified1969
def sourceMap1969swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1969swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1969swap_checked : acceptsGraphIso
    (source (graph core1969) (root 10) 2 0) DegreeTwoThreeSpectrum3752.graph sourceMap1969swap=true := by decide +kernel
theorem fusedMap1969swap_checked : acceptsGraphIso
    (fused (graph core1969) (root 10) 2 0) DegreeTwoThreeSpectrum3029.graph fusedMap1969swap=true := by decide +kernel
theorem certified1969swap : Certified (graph core1969) (root 10) 2 0 :=
  of_native_maps core1969 DegreeTwoThreeSpectrum3752.graph DegreeTwoThreeSpectrum3029.graph
    sourceMap1969swap fusedMap1969swap sourceMap1969swap_checked fusedMap1969swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1969
#print axioms sourceMap1969swap_checked
#print axioms fusedMap1969swap_checked
#print axioms certified1969swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
