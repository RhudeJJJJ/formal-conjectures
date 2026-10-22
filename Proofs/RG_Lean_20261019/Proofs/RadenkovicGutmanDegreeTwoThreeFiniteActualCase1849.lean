/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1849 : Family 10 := level10.get ⟨1254,by decide⟩
def sourceMap1849 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1849 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1849_checked : acceptsGraphIso
    (source (graph core1849) (root 10) 0 2) DegreeTwoThreeSpectrum3396.graph sourceMap1849=true := by decide +kernel
theorem fusedMap1849_checked : acceptsGraphIso
    (fused (graph core1849) (root 10) 0 2) DegreeTwoThreeSpectrum3397.graph fusedMap1849=true := by decide +kernel
theorem certified1849 : Certified (graph core1849) (root 10) 0 2 :=
  of_native_maps core1849 DegreeTwoThreeSpectrum3396.graph DegreeTwoThreeSpectrum3397.graph
    sourceMap1849 fusedMap1849 sourceMap1849_checked fusedMap1849_checked
    DegreeTwoThreeFiniteComparisons.comparison1849
#print axioms sourceMap1849_checked
#print axioms fusedMap1849_checked
#print axioms certified1849
def sourceMap1849swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1849swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1849swap_checked : acceptsGraphIso
    (source (graph core1849) (root 10) 2 0) DegreeTwoThreeSpectrum3396.graph sourceMap1849swap=true := by decide +kernel
theorem fusedMap1849swap_checked : acceptsGraphIso
    (fused (graph core1849) (root 10) 2 0) DegreeTwoThreeSpectrum3397.graph fusedMap1849swap=true := by decide +kernel
theorem certified1849swap : Certified (graph core1849) (root 10) 2 0 :=
  of_native_maps core1849 DegreeTwoThreeSpectrum3396.graph DegreeTwoThreeSpectrum3397.graph
    sourceMap1849swap fusedMap1849swap sourceMap1849swap_checked fusedMap1849swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1849
#print axioms sourceMap1849swap_checked
#print axioms fusedMap1849swap_checked
#print axioms certified1849swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
