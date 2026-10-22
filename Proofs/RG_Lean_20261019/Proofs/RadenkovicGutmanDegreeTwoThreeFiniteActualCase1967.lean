/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1967 : Family 10 := level10.get ⟨1547,by decide⟩
def sourceMap1967 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1967 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1967_checked : acceptsGraphIso
    (source (graph core1967) (root 10) 0 2) DegreeTwoThreeSpectrum3750.graph sourceMap1967=true := by decide +kernel
theorem fusedMap1967_checked : acceptsGraphIso
    (fused (graph core1967) (root 10) 0 2) DegreeTwoThreeSpectrum3024.graph fusedMap1967=true := by decide +kernel
theorem certified1967 : Certified (graph core1967) (root 10) 0 2 :=
  of_native_maps core1967 DegreeTwoThreeSpectrum3750.graph DegreeTwoThreeSpectrum3024.graph
    sourceMap1967 fusedMap1967 sourceMap1967_checked fusedMap1967_checked
    DegreeTwoThreeFiniteComparisons.comparison1967
#print axioms sourceMap1967_checked
#print axioms fusedMap1967_checked
#print axioms certified1967
def sourceMap1967swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1967swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1967swap_checked : acceptsGraphIso
    (source (graph core1967) (root 10) 2 0) DegreeTwoThreeSpectrum3750.graph sourceMap1967swap=true := by decide +kernel
theorem fusedMap1967swap_checked : acceptsGraphIso
    (fused (graph core1967) (root 10) 2 0) DegreeTwoThreeSpectrum3024.graph fusedMap1967swap=true := by decide +kernel
theorem certified1967swap : Certified (graph core1967) (root 10) 2 0 :=
  of_native_maps core1967 DegreeTwoThreeSpectrum3750.graph DegreeTwoThreeSpectrum3024.graph
    sourceMap1967swap fusedMap1967swap sourceMap1967swap_checked fusedMap1967swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1967
#print axioms sourceMap1967swap_checked
#print axioms fusedMap1967swap_checked
#print axioms certified1967swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
