/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0092 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0092 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,5,6,7,2,3,4,0,8,9,10,11,12] (sourceLabel 3 2 5 v)
def fusedMap0092 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 2 5 v)
theorem sourceMap0092_checked : acceptsGraphIso
    (source (graph core0092) (root 3) 2 5) DegreeOneSmallSpectrum946.graph sourceMap0092=true := by decide +kernel
theorem fusedMap0092_checked : acceptsGraphIso
    (fused (graph core0092) (root 3) 2 5) DegreeOneSmallSpectrum856.graph fusedMap0092=true := by decide +kernel
theorem certified0092 : Certified (graph core0092) (root 3) 2 5 :=
  of_native_maps core0092 DegreeOneSmallSpectrum946.graph DegreeOneSmallSpectrum856.graph
    sourceMap0092 fusedMap0092 sourceMap0092_checked fusedMap0092_checked
    DegreeOneSmallComparisons.comparison0092
#print axioms sourceMap0092_checked
#print axioms fusedMap0092_checked
#print axioms certified0092
def sourceMap0092swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,5,6,7,0,8,9,10,11,12,2,3,4] (sourceLabel 3 5 2 v)
def fusedMap0092swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 5 2 v)
theorem sourceMap0092swap_checked : acceptsGraphIso
    (source (graph core0092) (root 3) 5 2) DegreeOneSmallSpectrum946.graph sourceMap0092swap=true := by decide +kernel
theorem fusedMap0092swap_checked : acceptsGraphIso
    (fused (graph core0092) (root 3) 5 2) DegreeOneSmallSpectrum856.graph fusedMap0092swap=true := by decide +kernel
theorem certified0092swap : Certified (graph core0092) (root 3) 5 2 :=
  of_native_maps core0092 DegreeOneSmallSpectrum946.graph DegreeOneSmallSpectrum856.graph
    sourceMap0092swap fusedMap0092swap sourceMap0092swap_checked fusedMap0092swap_checked
    DegreeOneSmallComparisons.comparison0092
#print axioms sourceMap0092swap_checked
#print axioms fusedMap0092swap_checked
#print axioms certified0092swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
