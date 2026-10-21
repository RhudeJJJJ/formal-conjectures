/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0065 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0065 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 3 1 3 v)
def fusedMap0065 : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![1,2,3,4,0,5,6,7,8,9] (fusedLabel 3 1 3 v)
theorem sourceMap0065_checked : acceptsGraphIso
    (source (graph core0065) (root 3) 1 3) DegreeOneSmallSpectrum087.graph sourceMap0065=true := by decide +kernel
theorem fusedMap0065_checked : acceptsGraphIso
    (fused (graph core0065) (root 3) 1 3) DegreeOneSmallSpectrum073.graph fusedMap0065=true := by decide +kernel
theorem certified0065 : Certified (graph core0065) (root 3) 1 3 :=
  of_native_maps core0065 DegreeOneSmallSpectrum087.graph DegreeOneSmallSpectrum073.graph
    sourceMap0065 fusedMap0065 sourceMap0065_checked fusedMap0065_checked
    DegreeOneSmallComparisons.comparison0065
#print axioms sourceMap0065_checked
#print axioms fusedMap0065_checked
#print axioms certified0065
def sourceMap0065swap : (Vertices 3 ⊕ Fin 4 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,6,7,8,9,4,5] (sourceLabel 3 3 1 v)
def fusedMap0065swap : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![1,2,3,4,0,5,6,7,8,9] (fusedLabel 3 3 1 v)
theorem sourceMap0065swap_checked : acceptsGraphIso
    (source (graph core0065) (root 3) 3 1) DegreeOneSmallSpectrum087.graph sourceMap0065swap=true := by decide +kernel
theorem fusedMap0065swap_checked : acceptsGraphIso
    (fused (graph core0065) (root 3) 3 1) DegreeOneSmallSpectrum073.graph fusedMap0065swap=true := by decide +kernel
theorem certified0065swap : Certified (graph core0065) (root 3) 3 1 :=
  of_native_maps core0065 DegreeOneSmallSpectrum087.graph DegreeOneSmallSpectrum073.graph
    sourceMap0065swap fusedMap0065swap sourceMap0065swap_checked fusedMap0065swap_checked
    DegreeOneSmallComparisons.comparison0065
#print axioms sourceMap0065swap_checked
#print axioms fusedMap0065swap_checked
#print axioms certified0065swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
