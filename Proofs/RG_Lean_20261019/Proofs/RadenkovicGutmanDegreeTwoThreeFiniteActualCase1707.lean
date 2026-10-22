/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1707 : Family 10 := level10.get ⟨902,by decide⟩
def sourceMap1707 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,6,2,3,4] (sourceLabel 10 0 2 v)
def fusedMap1707 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1707_checked : acceptsGraphIso
    (source (graph core1707) (root 10) 0 2) DegreeTwoThreeSpectrum3704.graph sourceMap1707=true := by decide +kernel
theorem fusedMap1707_checked : acceptsGraphIso
    (fused (graph core1707) (root 10) 0 2) DegreeTwoThreeSpectrum2915.graph fusedMap1707=true := by decide +kernel
theorem certified1707 : Certified (graph core1707) (root 10) 0 2 :=
  of_native_maps core1707 DegreeTwoThreeSpectrum3704.graph DegreeTwoThreeSpectrum2915.graph
    sourceMap1707 fusedMap1707 sourceMap1707_checked fusedMap1707_checked
    DegreeTwoThreeFiniteComparisons.comparison1707
#print axioms sourceMap1707_checked
#print axioms fusedMap1707_checked
#print axioms certified1707
def sourceMap1707swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,7,8,9,10,11,12,13,14,5,2,3,4,6] (sourceLabel 10 2 0 v)
def fusedMap1707swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1707swap_checked : acceptsGraphIso
    (source (graph core1707) (root 10) 2 0) DegreeTwoThreeSpectrum3704.graph sourceMap1707swap=true := by decide +kernel
theorem fusedMap1707swap_checked : acceptsGraphIso
    (fused (graph core1707) (root 10) 2 0) DegreeTwoThreeSpectrum2915.graph fusedMap1707swap=true := by decide +kernel
theorem certified1707swap : Certified (graph core1707) (root 10) 2 0 :=
  of_native_maps core1707 DegreeTwoThreeSpectrum3704.graph DegreeTwoThreeSpectrum2915.graph
    sourceMap1707swap fusedMap1707swap sourceMap1707swap_checked fusedMap1707swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1707
#print axioms sourceMap1707swap_checked
#print axioms fusedMap1707swap_checked
#print axioms certified1707swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
