/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1322 : Family 9 := level9.get ⟨81,by decide⟩
def sourceMap1322 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1322 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1322_checked : acceptsGraphIso
    (source (graph core1322) (root 9) 0 1) DegreeOneSmallSpectrum1426.graph sourceMap1322=true := by decide +kernel
theorem fusedMap1322_checked : acceptsGraphIso
    (fused (graph core1322) (root 9) 0 1) DegreeOneSmallSpectrum925.graph fusedMap1322=true := by decide +kernel
theorem certified1322 : Certified (graph core1322) (root 9) 0 1 :=
  of_native_maps core1322 DegreeOneSmallSpectrum1426.graph DegreeOneSmallSpectrum925.graph
    sourceMap1322 fusedMap1322 sourceMap1322_checked fusedMap1322_checked
    DegreeOneSmallComparisons.comparison1322
#print axioms sourceMap1322_checked
#print axioms fusedMap1322_checked
#print axioms certified1322
def sourceMap1322swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1322swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1322swap_checked : acceptsGraphIso
    (source (graph core1322) (root 9) 1 0) DegreeOneSmallSpectrum1426.graph sourceMap1322swap=true := by decide +kernel
theorem fusedMap1322swap_checked : acceptsGraphIso
    (fused (graph core1322) (root 9) 1 0) DegreeOneSmallSpectrum925.graph fusedMap1322swap=true := by decide +kernel
theorem certified1322swap : Certified (graph core1322) (root 9) 1 0 :=
  of_native_maps core1322 DegreeOneSmallSpectrum1426.graph DegreeOneSmallSpectrum925.graph
    sourceMap1322swap fusedMap1322swap sourceMap1322swap_checked fusedMap1322swap_checked
    DegreeOneSmallComparisons.comparison1322
#print axioms sourceMap1322swap_checked
#print axioms fusedMap1322swap_checked
#print axioms certified1322swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
