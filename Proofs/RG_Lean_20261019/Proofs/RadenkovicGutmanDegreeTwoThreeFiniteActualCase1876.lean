/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1876 : Family 10 := level10.get ⟨1319,by decide⟩
def sourceMap1876 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1876 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1876_checked : acceptsGraphIso
    (source (graph core1876) (root 10) 0 2) DegreeTwoThreeSpectrum3492.graph sourceMap1876=true := by decide +kernel
theorem fusedMap1876_checked : acceptsGraphIso
    (fused (graph core1876) (root 10) 0 2) DegreeTwoThreeSpectrum3493.graph fusedMap1876=true := by decide +kernel
theorem certified1876 : Certified (graph core1876) (root 10) 0 2 :=
  of_native_maps core1876 DegreeTwoThreeSpectrum3492.graph DegreeTwoThreeSpectrum3493.graph
    sourceMap1876 fusedMap1876 sourceMap1876_checked fusedMap1876_checked
    DegreeTwoThreeFiniteComparisons.comparison1876
#print axioms sourceMap1876_checked
#print axioms fusedMap1876_checked
#print axioms certified1876
def sourceMap1876swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1876swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1876swap_checked : acceptsGraphIso
    (source (graph core1876) (root 10) 2 0) DegreeTwoThreeSpectrum3492.graph sourceMap1876swap=true := by decide +kernel
theorem fusedMap1876swap_checked : acceptsGraphIso
    (fused (graph core1876) (root 10) 2 0) DegreeTwoThreeSpectrum3493.graph fusedMap1876swap=true := by decide +kernel
theorem certified1876swap : Certified (graph core1876) (root 10) 2 0 :=
  of_native_maps core1876 DegreeTwoThreeSpectrum3492.graph DegreeTwoThreeSpectrum3493.graph
    sourceMap1876swap fusedMap1876swap sourceMap1876swap_checked fusedMap1876swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1876
#print axioms sourceMap1876swap_checked
#print axioms fusedMap1876swap_checked
#print axioms certified1876swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
