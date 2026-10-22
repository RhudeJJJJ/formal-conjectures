/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1987 : Family 10 := level10.get ⟨1588,by decide⟩
def sourceMap1987 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1987 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1987_checked : acceptsGraphIso
    (source (graph core1987) (root 10) 0 2) DegreeTwoThreeSpectrum3771.graph sourceMap1987=true := by decide +kernel
theorem fusedMap1987_checked : acceptsGraphIso
    (fused (graph core1987) (root 10) 0 2) DegreeTwoThreeSpectrum3087.graph fusedMap1987=true := by decide +kernel
theorem certified1987 : Certified (graph core1987) (root 10) 0 2 :=
  of_native_maps core1987 DegreeTwoThreeSpectrum3771.graph DegreeTwoThreeSpectrum3087.graph
    sourceMap1987 fusedMap1987 sourceMap1987_checked fusedMap1987_checked
    DegreeTwoThreeFiniteComparisons.comparison1987
#print axioms sourceMap1987_checked
#print axioms fusedMap1987_checked
#print axioms certified1987
def sourceMap1987swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1987swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1987swap_checked : acceptsGraphIso
    (source (graph core1987) (root 10) 2 0) DegreeTwoThreeSpectrum3771.graph sourceMap1987swap=true := by decide +kernel
theorem fusedMap1987swap_checked : acceptsGraphIso
    (fused (graph core1987) (root 10) 2 0) DegreeTwoThreeSpectrum3087.graph fusedMap1987swap=true := by decide +kernel
theorem certified1987swap : Certified (graph core1987) (root 10) 2 0 :=
  of_native_maps core1987 DegreeTwoThreeSpectrum3771.graph DegreeTwoThreeSpectrum3087.graph
    sourceMap1987swap fusedMap1987swap sourceMap1987swap_checked fusedMap1987swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1987
#print axioms sourceMap1987swap_checked
#print axioms fusedMap1987swap_checked
#print axioms certified1987swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
