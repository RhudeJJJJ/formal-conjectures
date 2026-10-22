/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1418 : Family 9 := level9.get ⟨644,by decide⟩
def sourceMap1418 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,6,7,8] (sourceLabel 9 0 2 v)
def fusedMap1418 : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 0 2 v)
theorem sourceMap1418_checked : acceptsGraphIso
    (source (graph core1418) (root 9) 0 2) DegreeTwoThreeSpectrum2294.graph sourceMap1418=true := by decide +kernel
theorem fusedMap1418_checked : acceptsGraphIso
    (fused (graph core1418) (root 9) 0 2) DegreeTwoThreeSpectrum2097.graph fusedMap1418=true := by decide +kernel
theorem certified1418 : Certified (graph core1418) (root 9) 0 2 :=
  of_native_maps core1418 DegreeTwoThreeSpectrum2294.graph DegreeTwoThreeSpectrum2097.graph
    sourceMap1418 fusedMap1418 sourceMap1418_checked fusedMap1418_checked
    DegreeTwoThreeFiniteComparisons.comparison1418
#print axioms sourceMap1418_checked
#print axioms fusedMap1418_checked
#print axioms certified1418
def sourceMap1418swap : (Vertices 9 ⊕ Fin 3 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,6,7,8,13] (sourceLabel 9 2 0 v)
def fusedMap1418swap : (Vertices 9 ⊕ Fin 4) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 9 2 0 v)
theorem sourceMap1418swap_checked : acceptsGraphIso
    (source (graph core1418) (root 9) 2 0) DegreeTwoThreeSpectrum2294.graph sourceMap1418swap=true := by decide +kernel
theorem fusedMap1418swap_checked : acceptsGraphIso
    (fused (graph core1418) (root 9) 2 0) DegreeTwoThreeSpectrum2097.graph fusedMap1418swap=true := by decide +kernel
theorem certified1418swap : Certified (graph core1418) (root 9) 2 0 :=
  of_native_maps core1418 DegreeTwoThreeSpectrum2294.graph DegreeTwoThreeSpectrum2097.graph
    sourceMap1418swap fusedMap1418swap sourceMap1418swap_checked fusedMap1418swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1418
#print axioms sourceMap1418swap_checked
#print axioms fusedMap1418swap_checked
#print axioms certified1418swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
