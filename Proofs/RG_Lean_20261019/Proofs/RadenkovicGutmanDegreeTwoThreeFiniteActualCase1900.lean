/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1900 : Family 10 := level10.get ⟨1372,by decide⟩
def sourceMap1900 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1900 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1900_checked : acceptsGraphIso
    (source (graph core1900) (root 10) 0 2) DegreeTwoThreeSpectrum3567.graph sourceMap1900=true := by decide +kernel
theorem fusedMap1900_checked : acceptsGraphIso
    (fused (graph core1900) (root 10) 0 2) DegreeTwoThreeSpectrum3569.graph fusedMap1900=true := by decide +kernel
theorem certified1900 : Certified (graph core1900) (root 10) 0 2 :=
  of_native_maps core1900 DegreeTwoThreeSpectrum3567.graph DegreeTwoThreeSpectrum3569.graph
    sourceMap1900 fusedMap1900 sourceMap1900_checked fusedMap1900_checked
    DegreeTwoThreeFiniteComparisons.comparison1900
#print axioms sourceMap1900_checked
#print axioms fusedMap1900_checked
#print axioms certified1900
def sourceMap1900swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1900swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1900swap_checked : acceptsGraphIso
    (source (graph core1900) (root 10) 2 0) DegreeTwoThreeSpectrum3567.graph sourceMap1900swap=true := by decide +kernel
theorem fusedMap1900swap_checked : acceptsGraphIso
    (fused (graph core1900) (root 10) 2 0) DegreeTwoThreeSpectrum3569.graph fusedMap1900swap=true := by decide +kernel
theorem certified1900swap : Certified (graph core1900) (root 10) 2 0 :=
  of_native_maps core1900 DegreeTwoThreeSpectrum3567.graph DegreeTwoThreeSpectrum3569.graph
    sourceMap1900swap fusedMap1900swap sourceMap1900swap_checked fusedMap1900swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1900
#print axioms sourceMap1900swap_checked
#print axioms fusedMap1900swap_checked
#print axioms certified1900swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
