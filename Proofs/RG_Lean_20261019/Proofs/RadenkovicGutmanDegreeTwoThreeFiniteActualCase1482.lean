/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1482 : Family 10 := level10.get ⟨230,by decide⟩
def sourceMap1482 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1482 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1482_checked : acceptsGraphIso
    (source (graph core1482) (root 10) 0 2) DegreeTwoThreeSpectrum2542.graph sourceMap1482=true := by decide +kernel
theorem fusedMap1482_checked : acceptsGraphIso
    (fused (graph core1482) (root 10) 0 2) DegreeTwoThreeSpectrum2544.graph fusedMap1482=true := by decide +kernel
theorem certified1482 : Certified (graph core1482) (root 10) 0 2 :=
  of_native_maps core1482 DegreeTwoThreeSpectrum2542.graph DegreeTwoThreeSpectrum2544.graph
    sourceMap1482 fusedMap1482 sourceMap1482_checked fusedMap1482_checked
    DegreeTwoThreeFiniteComparisons.comparison1482
#print axioms sourceMap1482_checked
#print axioms fusedMap1482_checked
#print axioms certified1482
def sourceMap1482swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1482swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1482swap_checked : acceptsGraphIso
    (source (graph core1482) (root 10) 2 0) DegreeTwoThreeSpectrum2542.graph sourceMap1482swap=true := by decide +kernel
theorem fusedMap1482swap_checked : acceptsGraphIso
    (fused (graph core1482) (root 10) 2 0) DegreeTwoThreeSpectrum2544.graph fusedMap1482swap=true := by decide +kernel
theorem certified1482swap : Certified (graph core1482) (root 10) 2 0 :=
  of_native_maps core1482 DegreeTwoThreeSpectrum2542.graph DegreeTwoThreeSpectrum2544.graph
    sourceMap1482swap fusedMap1482swap sourceMap1482swap_checked fusedMap1482swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1482
#print axioms sourceMap1482swap_checked
#print axioms fusedMap1482swap_checked
#print axioms certified1482swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
