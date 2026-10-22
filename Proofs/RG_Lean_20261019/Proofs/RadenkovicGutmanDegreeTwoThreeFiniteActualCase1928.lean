/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1928 : Family 10 := level10.get ⟨1439,by decide⟩
def sourceMap1928 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1928 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1928_checked : acceptsGraphIso
    (source (graph core1928) (root 10) 0 2) DegreeTwoThreeSpectrum3668.graph sourceMap1928=true := by decide +kernel
theorem fusedMap1928_checked : acceptsGraphIso
    (fused (graph core1928) (root 10) 0 2) DegreeTwoThreeSpectrum3670.graph fusedMap1928=true := by decide +kernel
theorem certified1928 : Certified (graph core1928) (root 10) 0 2 :=
  of_native_maps core1928 DegreeTwoThreeSpectrum3668.graph DegreeTwoThreeSpectrum3670.graph
    sourceMap1928 fusedMap1928 sourceMap1928_checked fusedMap1928_checked
    DegreeTwoThreeFiniteComparisons.comparison1928
#print axioms sourceMap1928_checked
#print axioms fusedMap1928_checked
#print axioms certified1928
def sourceMap1928swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1928swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1928swap_checked : acceptsGraphIso
    (source (graph core1928) (root 10) 2 0) DegreeTwoThreeSpectrum3668.graph sourceMap1928swap=true := by decide +kernel
theorem fusedMap1928swap_checked : acceptsGraphIso
    (fused (graph core1928) (root 10) 2 0) DegreeTwoThreeSpectrum3670.graph fusedMap1928swap=true := by decide +kernel
theorem certified1928swap : Certified (graph core1928) (root 10) 2 0 :=
  of_native_maps core1928 DegreeTwoThreeSpectrum3668.graph DegreeTwoThreeSpectrum3670.graph
    sourceMap1928swap fusedMap1928swap sourceMap1928swap_checked fusedMap1928swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1928
#print axioms sourceMap1928swap_checked
#print axioms fusedMap1928swap_checked
#print axioms certified1928swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
