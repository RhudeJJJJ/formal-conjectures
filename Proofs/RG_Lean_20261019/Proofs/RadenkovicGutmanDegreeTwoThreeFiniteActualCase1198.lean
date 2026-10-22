/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1198 : Family 9 := level9.get ⟨40,by decide⟩
def sourceMap1198 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![2,1,0,9,10,11,12,13,8,6,7,3,4,5] (sourceLabel 9 0 2 v)
def fusedMap1198 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,7,6,2,3,4,5] (fusedLabel 9 0 2 v)
theorem sourceMap1198_checked : acceptsGraphIso
    (source (graph core1198) (root 9) 0 2) DegreeTwoThreeSpectrum1882.graph sourceMap1198=true := by decide +kernel
theorem fusedMap1198_checked : acceptsGraphIso
    (fused (graph core1198) (root 9) 0 2) DegreeTwoThreeSpectrum1731.graph fusedMap1198=true := by decide +kernel
theorem certified1198 : Certified (graph core1198) (root 9) 0 2 :=
  of_native_maps core1198 DegreeTwoThreeSpectrum1882.graph DegreeTwoThreeSpectrum1731.graph
    sourceMap1198 fusedMap1198 sourceMap1198_checked fusedMap1198_checked
    DegreeTwoThreeFiniteComparisons.comparison1198
#print axioms sourceMap1198_checked
#print axioms fusedMap1198_checked
#print axioms certified1198
def sourceMap1198swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,1,0,9,10,11,12,13,8,6,3,4,5,7] (sourceLabel 9 2 0 v)
def fusedMap1198swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,7,6,2,3,4,5] (fusedLabel 9 2 0 v)
theorem sourceMap1198swap_checked : acceptsGraphIso
    (source (graph core1198) (root 9) 2 0) DegreeTwoThreeSpectrum1882.graph sourceMap1198swap=true := by decide +kernel
theorem fusedMap1198swap_checked : acceptsGraphIso
    (fused (graph core1198) (root 9) 2 0) DegreeTwoThreeSpectrum1731.graph fusedMap1198swap=true := by decide +kernel
theorem certified1198swap : Certified (graph core1198) (root 9) 2 0 :=
  of_native_maps core1198 DegreeTwoThreeSpectrum1882.graph DegreeTwoThreeSpectrum1731.graph
    sourceMap1198swap fusedMap1198swap sourceMap1198swap_checked fusedMap1198swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1198
#print axioms sourceMap1198swap_checked
#print axioms fusedMap1198swap_checked
#print axioms certified1198swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
