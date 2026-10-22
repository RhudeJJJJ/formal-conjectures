/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1886 : Family 10 := level10.get ⟨1338,by decide⟩
def sourceMap1886 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1886 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1886_checked : acceptsGraphIso
    (source (graph core1886) (root 10) 0 2) DegreeTwoThreeSpectrum3515.graph sourceMap1886=true := by decide +kernel
theorem fusedMap1886_checked : acceptsGraphIso
    (fused (graph core1886) (root 10) 0 2) DegreeTwoThreeSpectrum3525.graph fusedMap1886=true := by decide +kernel
theorem certified1886 : Certified (graph core1886) (root 10) 0 2 :=
  of_native_maps core1886 DegreeTwoThreeSpectrum3515.graph DegreeTwoThreeSpectrum3525.graph
    sourceMap1886 fusedMap1886 sourceMap1886_checked fusedMap1886_checked
    DegreeTwoThreeFiniteComparisons.comparison1886
#print axioms sourceMap1886_checked
#print axioms fusedMap1886_checked
#print axioms certified1886
def sourceMap1886swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1886swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1886swap_checked : acceptsGraphIso
    (source (graph core1886) (root 10) 2 0) DegreeTwoThreeSpectrum3515.graph sourceMap1886swap=true := by decide +kernel
theorem fusedMap1886swap_checked : acceptsGraphIso
    (fused (graph core1886) (root 10) 2 0) DegreeTwoThreeSpectrum3525.graph fusedMap1886swap=true := by decide +kernel
theorem certified1886swap : Certified (graph core1886) (root 10) 2 0 :=
  of_native_maps core1886 DegreeTwoThreeSpectrum3515.graph DegreeTwoThreeSpectrum3525.graph
    sourceMap1886swap fusedMap1886swap sourceMap1886swap_checked fusedMap1886swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1886
#print axioms sourceMap1886swap_checked
#print axioms fusedMap1886swap_checked
#print axioms certified1886swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
