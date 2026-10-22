/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1916 : Family 10 := level10.get ⟨1411,by decide⟩
def sourceMap1916 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1916 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1916_checked : acceptsGraphIso
    (source (graph core1916) (root 10) 0 2) DegreeTwoThreeSpectrum3623.graph sourceMap1916=true := by decide +kernel
theorem fusedMap1916_checked : acceptsGraphIso
    (fused (graph core1916) (root 10) 0 2) DegreeTwoThreeSpectrum3628.graph fusedMap1916=true := by decide +kernel
theorem certified1916 : Certified (graph core1916) (root 10) 0 2 :=
  of_native_maps core1916 DegreeTwoThreeSpectrum3623.graph DegreeTwoThreeSpectrum3628.graph
    sourceMap1916 fusedMap1916 sourceMap1916_checked fusedMap1916_checked
    DegreeTwoThreeFiniteComparisons.comparison1916
#print axioms sourceMap1916_checked
#print axioms fusedMap1916_checked
#print axioms certified1916
def sourceMap1916swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1916swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1916swap_checked : acceptsGraphIso
    (source (graph core1916) (root 10) 2 0) DegreeTwoThreeSpectrum3623.graph sourceMap1916swap=true := by decide +kernel
theorem fusedMap1916swap_checked : acceptsGraphIso
    (fused (graph core1916) (root 10) 2 0) DegreeTwoThreeSpectrum3628.graph fusedMap1916swap=true := by decide +kernel
theorem certified1916swap : Certified (graph core1916) (root 10) 2 0 :=
  of_native_maps core1916 DegreeTwoThreeSpectrum3623.graph DegreeTwoThreeSpectrum3628.graph
    sourceMap1916swap fusedMap1916swap sourceMap1916swap_checked fusedMap1916swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1916
#print axioms sourceMap1916swap_checked
#print axioms fusedMap1916swap_checked
#print axioms certified1916swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
