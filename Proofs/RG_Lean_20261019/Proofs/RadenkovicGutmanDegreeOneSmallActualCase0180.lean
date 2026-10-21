/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0180 : Family 5 := level5.get ⟨1,by decide⟩
def sourceMap0180 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap0180 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap0180_checked : acceptsGraphIso
    (source (graph core0180) (root 5) 1 4) DegreeOneSmallSpectrum888.graph sourceMap0180=true := by decide +kernel
theorem fusedMap0180_checked : acceptsGraphIso
    (fused (graph core0180) (root 5) 1 4) DegreeOneSmallSpectrum856.graph fusedMap0180=true := by decide +kernel
theorem certified0180 : Certified (graph core0180) (root 5) 1 4 :=
  of_native_maps core0180 DegreeOneSmallSpectrum888.graph DegreeOneSmallSpectrum856.graph
    sourceMap0180 fusedMap0180 sourceMap0180_checked fusedMap0180_checked
    DegreeOneSmallComparisons.comparison0180
#print axioms sourceMap0180_checked
#print axioms fusedMap0180_checked
#print axioms certified0180
def sourceMap0180swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,12,6,7] (sourceLabel 5 4 1 v)
def fusedMap0180swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap0180swap_checked : acceptsGraphIso
    (source (graph core0180) (root 5) 4 1) DegreeOneSmallSpectrum888.graph sourceMap0180swap=true := by decide +kernel
theorem fusedMap0180swap_checked : acceptsGraphIso
    (fused (graph core0180) (root 5) 4 1) DegreeOneSmallSpectrum856.graph fusedMap0180swap=true := by decide +kernel
theorem certified0180swap : Certified (graph core0180) (root 5) 4 1 :=
  of_native_maps core0180 DegreeOneSmallSpectrum888.graph DegreeOneSmallSpectrum856.graph
    sourceMap0180swap fusedMap0180swap sourceMap0180swap_checked fusedMap0180swap_checked
    DegreeOneSmallComparisons.comparison0180
#print axioms sourceMap0180swap_checked
#print axioms fusedMap0180swap_checked
#print axioms certified0180swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
