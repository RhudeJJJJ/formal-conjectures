/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1065 : Family 8 := level8.get ⟨133,by decide⟩
def sourceMap1065 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1065 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1065_checked : acceptsGraphIso
    (source (graph core1065) (root 8) 0 2) DegreeOneSmallSpectrum1300.graph sourceMap1065=true := by decide +kernel
theorem fusedMap1065_checked : acceptsGraphIso
    (fused (graph core1065) (root 8) 0 2) DegreeOneSmallSpectrum1301.graph fusedMap1065=true := by decide +kernel
theorem certified1065 : Certified (graph core1065) (root 8) 0 2 :=
  of_native_maps core1065 DegreeOneSmallSpectrum1300.graph DegreeOneSmallSpectrum1301.graph
    sourceMap1065 fusedMap1065 sourceMap1065_checked fusedMap1065_checked
    DegreeOneSmallComparisons.comparison1065
#print axioms sourceMap1065_checked
#print axioms fusedMap1065_checked
#print axioms certified1065
def sourceMap1065swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1065swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1065swap_checked : acceptsGraphIso
    (source (graph core1065) (root 8) 2 0) DegreeOneSmallSpectrum1300.graph sourceMap1065swap=true := by decide +kernel
theorem fusedMap1065swap_checked : acceptsGraphIso
    (fused (graph core1065) (root 8) 2 0) DegreeOneSmallSpectrum1301.graph fusedMap1065swap=true := by decide +kernel
theorem certified1065swap : Certified (graph core1065) (root 8) 2 0 :=
  of_native_maps core1065 DegreeOneSmallSpectrum1300.graph DegreeOneSmallSpectrum1301.graph
    sourceMap1065swap fusedMap1065swap sourceMap1065swap_checked fusedMap1065swap_checked
    DegreeOneSmallComparisons.comparison1065
#print axioms sourceMap1065swap_checked
#print axioms fusedMap1065swap_checked
#print axioms certified1065swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
