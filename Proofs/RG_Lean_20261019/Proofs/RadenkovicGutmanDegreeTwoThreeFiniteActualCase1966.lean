/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1966 : Family 10 := level10.get ⟨1544,by decide⟩
def sourceMap1966 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1966 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1966_checked : acceptsGraphIso
    (source (graph core1966) (root 10) 0 2) DegreeTwoThreeSpectrum3749.graph sourceMap1966=true := by decide +kernel
theorem fusedMap1966_checked : acceptsGraphIso
    (fused (graph core1966) (root 10) 0 2) DegreeTwoThreeSpectrum3021.graph fusedMap1966=true := by decide +kernel
theorem certified1966 : Certified (graph core1966) (root 10) 0 2 :=
  of_native_maps core1966 DegreeTwoThreeSpectrum3749.graph DegreeTwoThreeSpectrum3021.graph
    sourceMap1966 fusedMap1966 sourceMap1966_checked fusedMap1966_checked
    DegreeTwoThreeFiniteComparisons.comparison1966
#print axioms sourceMap1966_checked
#print axioms fusedMap1966_checked
#print axioms certified1966
def sourceMap1966swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1966swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1966swap_checked : acceptsGraphIso
    (source (graph core1966) (root 10) 2 0) DegreeTwoThreeSpectrum3749.graph sourceMap1966swap=true := by decide +kernel
theorem fusedMap1966swap_checked : acceptsGraphIso
    (fused (graph core1966) (root 10) 2 0) DegreeTwoThreeSpectrum3021.graph fusedMap1966swap=true := by decide +kernel
theorem certified1966swap : Certified (graph core1966) (root 10) 2 0 :=
  of_native_maps core1966 DegreeTwoThreeSpectrum3749.graph DegreeTwoThreeSpectrum3021.graph
    sourceMap1966swap fusedMap1966swap sourceMap1966swap_checked fusedMap1966swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1966
#print axioms sourceMap1966swap_checked
#print axioms fusedMap1966swap_checked
#print axioms certified1966swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
