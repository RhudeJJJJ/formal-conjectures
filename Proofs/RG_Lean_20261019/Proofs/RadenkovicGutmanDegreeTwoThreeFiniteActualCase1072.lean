/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1072 : Family 7 := level7.get ⟨48,by decide⟩
def sourceMap1072 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,6,7,8] (sourceLabel 7 0 2 v)
def fusedMap1072 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,10,11,6,7,8,9] (fusedLabel 7 0 2 v)
theorem sourceMap1072_checked : acceptsGraphIso
    (source (graph core1072) (root 7) 0 2) DegreeOneSmallSpectrum554.graph sourceMap1072=true := by decide +kernel
theorem fusedMap1072_checked : acceptsGraphIso
    (fused (graph core1072) (root 7) 0 2) DegreeOneSmallSpectrum559.graph fusedMap1072=true := by decide +kernel
theorem certified1072 : Certified (graph core1072) (root 7) 0 2 :=
  of_native_maps core1072 DegreeOneSmallSpectrum554.graph DegreeOneSmallSpectrum559.graph
    sourceMap1072 fusedMap1072 sourceMap1072_checked fusedMap1072_checked
    DegreeTwoThreeFiniteComparisons.comparison1072
#print axioms sourceMap1072_checked
#print axioms fusedMap1072_checked
#print axioms certified1072
def sourceMap1072swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,6,7,8,11] (sourceLabel 7 2 0 v)
def fusedMap1072swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,10,11,6,7,8,9] (fusedLabel 7 2 0 v)
theorem sourceMap1072swap_checked : acceptsGraphIso
    (source (graph core1072) (root 7) 2 0) DegreeOneSmallSpectrum554.graph sourceMap1072swap=true := by decide +kernel
theorem fusedMap1072swap_checked : acceptsGraphIso
    (fused (graph core1072) (root 7) 2 0) DegreeOneSmallSpectrum559.graph fusedMap1072swap=true := by decide +kernel
theorem certified1072swap : Certified (graph core1072) (root 7) 2 0 :=
  of_native_maps core1072 DegreeOneSmallSpectrum554.graph DegreeOneSmallSpectrum559.graph
    sourceMap1072swap fusedMap1072swap sourceMap1072swap_checked fusedMap1072swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1072
#print axioms sourceMap1072swap_checked
#print axioms fusedMap1072swap_checked
#print axioms certified1072swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
