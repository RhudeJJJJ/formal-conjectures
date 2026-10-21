/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1418 : Family 9 := level9.get ⟨159,by decide⟩
def sourceMap1418 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1418 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1418_checked : acceptsGraphIso
    (source (graph core1418) (root 9) 0 1) DegreeOneSmallSpectrum1107.graph sourceMap1418=true := by decide +kernel
theorem fusedMap1418_checked : acceptsGraphIso
    (fused (graph core1418) (root 9) 0 1) DegreeOneSmallSpectrum1112.graph fusedMap1418=true := by decide +kernel
theorem certified1418 : Certified (graph core1418) (root 9) 0 1 :=
  of_native_maps core1418 DegreeOneSmallSpectrum1107.graph DegreeOneSmallSpectrum1112.graph
    sourceMap1418 fusedMap1418 sourceMap1418_checked fusedMap1418_checked
    DegreeOneSmallComparisons.comparison1418
#print axioms sourceMap1418_checked
#print axioms fusedMap1418_checked
#print axioms certified1418
def sourceMap1418swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1418swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1418swap_checked : acceptsGraphIso
    (source (graph core1418) (root 9) 1 0) DegreeOneSmallSpectrum1107.graph sourceMap1418swap=true := by decide +kernel
theorem fusedMap1418swap_checked : acceptsGraphIso
    (fused (graph core1418) (root 9) 1 0) DegreeOneSmallSpectrum1112.graph fusedMap1418swap=true := by decide +kernel
theorem certified1418swap : Certified (graph core1418) (root 9) 1 0 :=
  of_native_maps core1418 DegreeOneSmallSpectrum1107.graph DegreeOneSmallSpectrum1112.graph
    sourceMap1418swap fusedMap1418swap sourceMap1418swap_checked fusedMap1418swap_checked
    DegreeOneSmallComparisons.comparison1418
#print axioms sourceMap1418swap_checked
#print axioms fusedMap1418swap_checked
#print axioms certified1418swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
