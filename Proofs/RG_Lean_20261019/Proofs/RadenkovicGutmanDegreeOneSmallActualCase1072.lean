/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1072 : Family 8 := level8.get ⟨136,by decide⟩
def sourceMap1072 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (sourceLabel 8 0 1 v)
def fusedMap1072 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1072_checked : acceptsGraphIso
    (source (graph core1072) (root 8) 0 1) DegreeOneSmallSpectrum792.graph sourceMap1072=true := by decide +kernel
theorem fusedMap1072_checked : acceptsGraphIso
    (fused (graph core1072) (root 8) 0 1) DegreeOneSmallSpectrum506.graph fusedMap1072=true := by decide +kernel
theorem certified1072 : Certified (graph core1072) (root 8) 0 1 :=
  of_native_maps core1072 DegreeOneSmallSpectrum792.graph DegreeOneSmallSpectrum506.graph
    sourceMap1072 fusedMap1072 sourceMap1072_checked fusedMap1072_checked
    DegreeOneSmallComparisons.comparison1072
#print axioms sourceMap1072_checked
#print axioms fusedMap1072_checked
#print axioms certified1072
def sourceMap1072swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 8 1 0 v)
def fusedMap1072swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1072swap_checked : acceptsGraphIso
    (source (graph core1072) (root 8) 1 0) DegreeOneSmallSpectrum792.graph sourceMap1072swap=true := by decide +kernel
theorem fusedMap1072swap_checked : acceptsGraphIso
    (fused (graph core1072) (root 8) 1 0) DegreeOneSmallSpectrum506.graph fusedMap1072swap=true := by decide +kernel
theorem certified1072swap : Certified (graph core1072) (root 8) 1 0 :=
  of_native_maps core1072 DegreeOneSmallSpectrum792.graph DegreeOneSmallSpectrum506.graph
    sourceMap1072swap fusedMap1072swap sourceMap1072swap_checked fusedMap1072swap_checked
    DegreeOneSmallComparisons.comparison1072
#print axioms sourceMap1072swap_checked
#print axioms fusedMap1072swap_checked
#print axioms certified1072swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
