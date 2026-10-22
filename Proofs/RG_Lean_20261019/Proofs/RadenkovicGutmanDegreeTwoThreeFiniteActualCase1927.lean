/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1927 : Family 10 := level10.get ⟨1438,by decide⟩
def sourceMap1927 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1927 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1927_checked : acceptsGraphIso
    (source (graph core1927) (root 10) 0 2) DegreeTwoThreeSpectrum3666.graph sourceMap1927=true := by decide +kernel
theorem fusedMap1927_checked : acceptsGraphIso
    (fused (graph core1927) (root 10) 0 2) DegreeTwoThreeSpectrum3667.graph fusedMap1927=true := by decide +kernel
theorem certified1927 : Certified (graph core1927) (root 10) 0 2 :=
  of_native_maps core1927 DegreeTwoThreeSpectrum3666.graph DegreeTwoThreeSpectrum3667.graph
    sourceMap1927 fusedMap1927 sourceMap1927_checked fusedMap1927_checked
    DegreeTwoThreeFiniteComparisons.comparison1927
#print axioms sourceMap1927_checked
#print axioms fusedMap1927_checked
#print axioms certified1927
def sourceMap1927swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1927swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1927swap_checked : acceptsGraphIso
    (source (graph core1927) (root 10) 2 0) DegreeTwoThreeSpectrum3666.graph sourceMap1927swap=true := by decide +kernel
theorem fusedMap1927swap_checked : acceptsGraphIso
    (fused (graph core1927) (root 10) 2 0) DegreeTwoThreeSpectrum3667.graph fusedMap1927swap=true := by decide +kernel
theorem certified1927swap : Certified (graph core1927) (root 10) 2 0 :=
  of_native_maps core1927 DegreeTwoThreeSpectrum3666.graph DegreeTwoThreeSpectrum3667.graph
    sourceMap1927swap fusedMap1927swap sourceMap1927swap_checked fusedMap1927swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1927
#print axioms sourceMap1927swap_checked
#print axioms fusedMap1927swap_checked
#print axioms certified1927swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
