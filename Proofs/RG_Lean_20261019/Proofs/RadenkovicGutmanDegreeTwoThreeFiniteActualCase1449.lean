/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1449 : Family 10 := level10.get ⟨104,by decide⟩
def sourceMap1449 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1449 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1449_checked : acceptsGraphIso
    (source (graph core1449) (root 10) 0 2) DegreeTwoThreeSpectrum2765.graph sourceMap1449=true := by decide +kernel
theorem fusedMap1449_checked : acceptsGraphIso
    (fused (graph core1449) (root 10) 0 2) DegreeTwoThreeSpectrum2364.graph fusedMap1449=true := by decide +kernel
theorem certified1449 : Certified (graph core1449) (root 10) 0 2 :=
  of_native_maps core1449 DegreeTwoThreeSpectrum2765.graph DegreeTwoThreeSpectrum2364.graph
    sourceMap1449 fusedMap1449 sourceMap1449_checked fusedMap1449_checked
    DegreeTwoThreeFiniteComparisons.comparison1449
#print axioms sourceMap1449_checked
#print axioms fusedMap1449_checked
#print axioms certified1449
def sourceMap1449swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1449swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1449swap_checked : acceptsGraphIso
    (source (graph core1449) (root 10) 2 0) DegreeTwoThreeSpectrum2765.graph sourceMap1449swap=true := by decide +kernel
theorem fusedMap1449swap_checked : acceptsGraphIso
    (fused (graph core1449) (root 10) 2 0) DegreeTwoThreeSpectrum2364.graph fusedMap1449swap=true := by decide +kernel
theorem certified1449swap : Certified (graph core1449) (root 10) 2 0 :=
  of_native_maps core1449 DegreeTwoThreeSpectrum2765.graph DegreeTwoThreeSpectrum2364.graph
    sourceMap1449swap fusedMap1449swap sourceMap1449swap_checked fusedMap1449swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1449
#print axioms sourceMap1449swap_checked
#print axioms fusedMap1449swap_checked
#print axioms certified1449swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
