/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1935 : Family 10 := level10.get ⟨1451,by decide⟩
def sourceMap1935 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1935 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1935_checked : acceptsGraphIso
    (source (graph core1935) (root 10) 0 2) DegreeTwoThreeSpectrum3535.graph sourceMap1935=true := by decide +kernel
theorem fusedMap1935_checked : acceptsGraphIso
    (fused (graph core1935) (root 10) 0 2) DegreeTwoThreeSpectrum3691.graph fusedMap1935=true := by decide +kernel
theorem certified1935 : Certified (graph core1935) (root 10) 0 2 :=
  of_native_maps core1935 DegreeTwoThreeSpectrum3535.graph DegreeTwoThreeSpectrum3691.graph
    sourceMap1935 fusedMap1935 sourceMap1935_checked fusedMap1935_checked
    DegreeTwoThreeFiniteComparisons.comparison1935
#print axioms sourceMap1935_checked
#print axioms fusedMap1935_checked
#print axioms certified1935
def sourceMap1935swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1935swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1935swap_checked : acceptsGraphIso
    (source (graph core1935) (root 10) 2 0) DegreeTwoThreeSpectrum3535.graph sourceMap1935swap=true := by decide +kernel
theorem fusedMap1935swap_checked : acceptsGraphIso
    (fused (graph core1935) (root 10) 2 0) DegreeTwoThreeSpectrum3691.graph fusedMap1935swap=true := by decide +kernel
theorem certified1935swap : Certified (graph core1935) (root 10) 2 0 :=
  of_native_maps core1935 DegreeTwoThreeSpectrum3535.graph DegreeTwoThreeSpectrum3691.graph
    sourceMap1935swap fusedMap1935swap sourceMap1935swap_checked fusedMap1935swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1935
#print axioms sourceMap1935swap_checked
#print axioms fusedMap1935swap_checked
#print axioms certified1935swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
