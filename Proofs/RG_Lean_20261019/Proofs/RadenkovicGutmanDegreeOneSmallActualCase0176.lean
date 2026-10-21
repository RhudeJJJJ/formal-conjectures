/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0176 : Family 5 := level5.get ⟨1,by decide⟩
def sourceMap0176 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap0176 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap0176_checked : acceptsGraphIso
    (source (graph core0176) (root 5) 0 5) DegreeOneSmallSpectrum894.graph sourceMap0176=true := by decide +kernel
theorem fusedMap0176_checked : acceptsGraphIso
    (fused (graph core0176) (root 5) 0 5) DegreeOneSmallSpectrum856.graph fusedMap0176=true := by decide +kernel
theorem certified0176 : Certified (graph core0176) (root 5) 0 5 :=
  of_native_maps core0176 DegreeOneSmallSpectrum894.graph DegreeOneSmallSpectrum856.graph
    sourceMap0176 fusedMap0176 sourceMap0176_checked fusedMap0176_checked
    DegreeOneSmallComparisons.comparison0176
#print axioms sourceMap0176_checked
#print axioms fusedMap0176_checked
#print axioms certified0176
def sourceMap0176swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,8,9,10,11,12,7] (sourceLabel 5 5 0 v)
def fusedMap0176swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap0176swap_checked : acceptsGraphIso
    (source (graph core0176) (root 5) 5 0) DegreeOneSmallSpectrum894.graph sourceMap0176swap=true := by decide +kernel
theorem fusedMap0176swap_checked : acceptsGraphIso
    (fused (graph core0176) (root 5) 5 0) DegreeOneSmallSpectrum856.graph fusedMap0176swap=true := by decide +kernel
theorem certified0176swap : Certified (graph core0176) (root 5) 5 0 :=
  of_native_maps core0176 DegreeOneSmallSpectrum894.graph DegreeOneSmallSpectrum856.graph
    sourceMap0176swap fusedMap0176swap sourceMap0176swap_checked fusedMap0176swap_checked
    DegreeOneSmallComparisons.comparison0176
#print axioms sourceMap0176swap_checked
#print axioms fusedMap0176swap_checked
#print axioms certified0176swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
