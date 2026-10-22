/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1047 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap1047 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,7,8,9,10,4,5,6,1,2,3] (sourceLabel 6 0 2 v)
def fusedMap1047 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,9,10,5,6,7,8] (fusedLabel 6 0 2 v)
theorem sourceMap1047_checked : acceptsGraphIso
    (source (graph core1047) (root 6) 0 2) DegreeOneSmallSpectrum220.graph sourceMap1047=true := by decide +kernel
theorem fusedMap1047_checked : acceptsGraphIso
    (fused (graph core1047) (root 6) 0 2) DegreeOneSmallSpectrum228.graph fusedMap1047=true := by decide +kernel
theorem certified1047 : Certified (graph core1047) (root 6) 0 2 :=
  of_native_maps core1047 DegreeOneSmallSpectrum220.graph DegreeOneSmallSpectrum228.graph
    sourceMap1047 fusedMap1047 sourceMap1047_checked fusedMap1047_checked
    DegreeTwoThreeFiniteComparisons.comparison1047
#print axioms sourceMap1047_checked
#print axioms fusedMap1047_checked
#print axioms certified1047
def sourceMap1047swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,7,8,9,10,4,5,1,2,3,6] (sourceLabel 6 2 0 v)
def fusedMap1047swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,9,10,5,6,7,8] (fusedLabel 6 2 0 v)
theorem sourceMap1047swap_checked : acceptsGraphIso
    (source (graph core1047) (root 6) 2 0) DegreeOneSmallSpectrum220.graph sourceMap1047swap=true := by decide +kernel
theorem fusedMap1047swap_checked : acceptsGraphIso
    (fused (graph core1047) (root 6) 2 0) DegreeOneSmallSpectrum228.graph fusedMap1047swap=true := by decide +kernel
theorem certified1047swap : Certified (graph core1047) (root 6) 2 0 :=
  of_native_maps core1047 DegreeOneSmallSpectrum220.graph DegreeOneSmallSpectrum228.graph
    sourceMap1047swap fusedMap1047swap sourceMap1047swap_checked fusedMap1047swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1047
#print axioms sourceMap1047swap_checked
#print axioms fusedMap1047swap_checked
#print axioms certified1047swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
