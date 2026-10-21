/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0714 : Family 7 := level7.get ⟨81,by decide⟩
def sourceMap0714 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 0 3 v)
def fusedMap0714 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0714_checked : acceptsGraphIso
    (source (graph core0714) (root 7) 0 3) DegreeOneSmallSpectrum1293.graph sourceMap0714=true := by decide +kernel
theorem fusedMap0714_checked : acceptsGraphIso
    (fused (graph core0714) (root 7) 0 3) DegreeOneSmallSpectrum1296.graph fusedMap0714=true := by decide +kernel
theorem certified0714 : Certified (graph core0714) (root 7) 0 3 :=
  of_native_maps core0714 DegreeOneSmallSpectrum1293.graph DegreeOneSmallSpectrum1296.graph
    sourceMap0714 fusedMap0714 sourceMap0714_checked fusedMap0714_checked
    DegreeOneSmallComparisons.comparison0714
#print axioms sourceMap0714_checked
#print axioms fusedMap0714_checked
#print axioms certified0714
def sourceMap0714swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,8] (sourceLabel 7 3 0 v)
def fusedMap0714swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0714swap_checked : acceptsGraphIso
    (source (graph core0714) (root 7) 3 0) DegreeOneSmallSpectrum1293.graph sourceMap0714swap=true := by decide +kernel
theorem fusedMap0714swap_checked : acceptsGraphIso
    (fused (graph core0714) (root 7) 3 0) DegreeOneSmallSpectrum1296.graph fusedMap0714swap=true := by decide +kernel
theorem certified0714swap : Certified (graph core0714) (root 7) 3 0 :=
  of_native_maps core0714 DegreeOneSmallSpectrum1293.graph DegreeOneSmallSpectrum1296.graph
    sourceMap0714swap fusedMap0714swap sourceMap0714swap_checked fusedMap0714swap_checked
    DegreeOneSmallComparisons.comparison0714
#print axioms sourceMap0714swap_checked
#print axioms fusedMap0714swap_checked
#print axioms certified0714swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
