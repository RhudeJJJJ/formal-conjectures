/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1924 : Family 10 := level10.get ⟨1430,by decide⟩
def sourceMap1924 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1924 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1924_checked : acceptsGraphIso
    (source (graph core1924) (root 10) 0 2) DegreeTwoThreeSpectrum3655.graph sourceMap1924=true := by decide +kernel
theorem fusedMap1924_checked : acceptsGraphIso
    (fused (graph core1924) (root 10) 0 2) DegreeTwoThreeSpectrum3660.graph fusedMap1924=true := by decide +kernel
theorem certified1924 : Certified (graph core1924) (root 10) 0 2 :=
  of_native_maps core1924 DegreeTwoThreeSpectrum3655.graph DegreeTwoThreeSpectrum3660.graph
    sourceMap1924 fusedMap1924 sourceMap1924_checked fusedMap1924_checked
    DegreeTwoThreeFiniteComparisons.comparison1924
#print axioms sourceMap1924_checked
#print axioms fusedMap1924_checked
#print axioms certified1924
def sourceMap1924swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1924swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1924swap_checked : acceptsGraphIso
    (source (graph core1924) (root 10) 2 0) DegreeTwoThreeSpectrum3655.graph sourceMap1924swap=true := by decide +kernel
theorem fusedMap1924swap_checked : acceptsGraphIso
    (fused (graph core1924) (root 10) 2 0) DegreeTwoThreeSpectrum3660.graph fusedMap1924swap=true := by decide +kernel
theorem certified1924swap : Certified (graph core1924) (root 10) 2 0 :=
  of_native_maps core1924 DegreeTwoThreeSpectrum3655.graph DegreeTwoThreeSpectrum3660.graph
    sourceMap1924swap fusedMap1924swap sourceMap1924swap_checked fusedMap1924swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1924
#print axioms sourceMap1924swap_checked
#print axioms fusedMap1924swap_checked
#print axioms certified1924swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
