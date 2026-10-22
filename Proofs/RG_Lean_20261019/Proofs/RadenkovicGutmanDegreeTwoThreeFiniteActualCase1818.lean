/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1818 : Family 10 := level10.get ⟨1180,by decide⟩
def sourceMap1818 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1818 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1818_checked : acceptsGraphIso
    (source (graph core1818) (root 10) 0 2) DegreeTwoThreeSpectrum3285.graph sourceMap1818=true := by decide +kernel
theorem fusedMap1818_checked : acceptsGraphIso
    (fused (graph core1818) (root 10) 0 2) DegreeTwoThreeSpectrum3286.graph fusedMap1818=true := by decide +kernel
theorem certified1818 : Certified (graph core1818) (root 10) 0 2 :=
  of_native_maps core1818 DegreeTwoThreeSpectrum3285.graph DegreeTwoThreeSpectrum3286.graph
    sourceMap1818 fusedMap1818 sourceMap1818_checked fusedMap1818_checked
    DegreeTwoThreeFiniteComparisons.comparison1818
#print axioms sourceMap1818_checked
#print axioms fusedMap1818_checked
#print axioms certified1818
def sourceMap1818swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1818swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1818swap_checked : acceptsGraphIso
    (source (graph core1818) (root 10) 2 0) DegreeTwoThreeSpectrum3285.graph sourceMap1818swap=true := by decide +kernel
theorem fusedMap1818swap_checked : acceptsGraphIso
    (fused (graph core1818) (root 10) 2 0) DegreeTwoThreeSpectrum3286.graph fusedMap1818swap=true := by decide +kernel
theorem certified1818swap : Certified (graph core1818) (root 10) 2 0 :=
  of_native_maps core1818 DegreeTwoThreeSpectrum3285.graph DegreeTwoThreeSpectrum3286.graph
    sourceMap1818swap fusedMap1818swap sourceMap1818swap_checked fusedMap1818swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1818
#print axioms sourceMap1818swap_checked
#print axioms fusedMap1818swap_checked
#print axioms certified1818swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
