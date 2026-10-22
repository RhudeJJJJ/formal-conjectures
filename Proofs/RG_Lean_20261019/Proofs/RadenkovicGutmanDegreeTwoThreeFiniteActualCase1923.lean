/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1923 : Family 10 := level10.get ⟨1429,by decide⟩
def sourceMap1923 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1923 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1923_checked : acceptsGraphIso
    (source (graph core1923) (root 10) 0 2) DegreeTwoThreeSpectrum3652.graph sourceMap1923=true := by decide +kernel
theorem fusedMap1923_checked : acceptsGraphIso
    (fused (graph core1923) (root 10) 0 2) DegreeTwoThreeSpectrum3653.graph fusedMap1923=true := by decide +kernel
theorem certified1923 : Certified (graph core1923) (root 10) 0 2 :=
  of_native_maps core1923 DegreeTwoThreeSpectrum3652.graph DegreeTwoThreeSpectrum3653.graph
    sourceMap1923 fusedMap1923 sourceMap1923_checked fusedMap1923_checked
    DegreeTwoThreeFiniteComparisons.comparison1923
#print axioms sourceMap1923_checked
#print axioms fusedMap1923_checked
#print axioms certified1923
def sourceMap1923swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1923swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1923swap_checked : acceptsGraphIso
    (source (graph core1923) (root 10) 2 0) DegreeTwoThreeSpectrum3652.graph sourceMap1923swap=true := by decide +kernel
theorem fusedMap1923swap_checked : acceptsGraphIso
    (fused (graph core1923) (root 10) 2 0) DegreeTwoThreeSpectrum3653.graph fusedMap1923swap=true := by decide +kernel
theorem certified1923swap : Certified (graph core1923) (root 10) 2 0 :=
  of_native_maps core1923 DegreeTwoThreeSpectrum3652.graph DegreeTwoThreeSpectrum3653.graph
    sourceMap1923swap fusedMap1923swap sourceMap1923swap_checked fusedMap1923swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1923
#print axioms sourceMap1923swap_checked
#print axioms fusedMap1923swap_checked
#print axioms certified1923swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
