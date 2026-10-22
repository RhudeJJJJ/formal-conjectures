/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1853 : Family 10 := level10.get ⟨1263,by decide⟩
def sourceMap1853 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1853 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1853_checked : acceptsGraphIso
    (source (graph core1853) (root 10) 0 2) DegreeTwoThreeSpectrum3409.graph sourceMap1853=true := by decide +kernel
theorem fusedMap1853_checked : acceptsGraphIso
    (fused (graph core1853) (root 10) 0 2) DegreeTwoThreeSpectrum3411.graph fusedMap1853=true := by decide +kernel
theorem certified1853 : Certified (graph core1853) (root 10) 0 2 :=
  of_native_maps core1853 DegreeTwoThreeSpectrum3409.graph DegreeTwoThreeSpectrum3411.graph
    sourceMap1853 fusedMap1853 sourceMap1853_checked fusedMap1853_checked
    DegreeTwoThreeFiniteComparisons.comparison1853
#print axioms sourceMap1853_checked
#print axioms fusedMap1853_checked
#print axioms certified1853
def sourceMap1853swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1853swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1853swap_checked : acceptsGraphIso
    (source (graph core1853) (root 10) 2 0) DegreeTwoThreeSpectrum3409.graph sourceMap1853swap=true := by decide +kernel
theorem fusedMap1853swap_checked : acceptsGraphIso
    (fused (graph core1853) (root 10) 2 0) DegreeTwoThreeSpectrum3411.graph fusedMap1853swap=true := by decide +kernel
theorem certified1853swap : Certified (graph core1853) (root 10) 2 0 :=
  of_native_maps core1853 DegreeTwoThreeSpectrum3409.graph DegreeTwoThreeSpectrum3411.graph
    sourceMap1853swap fusedMap1853swap sourceMap1853swap_checked fusedMap1853swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1853
#print axioms sourceMap1853swap_checked
#print axioms fusedMap1853swap_checked
#print axioms certified1853swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
