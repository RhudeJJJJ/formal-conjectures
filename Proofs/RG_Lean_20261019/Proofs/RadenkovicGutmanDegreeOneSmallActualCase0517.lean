/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0517 : Family 7 := level7.get ⟨13,by decide⟩
def sourceMap0517 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0517 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0517_checked : acceptsGraphIso
    (source (graph core0517) (root 7) 1 1) DegreeOneSmallSpectrum512.graph sourceMap0517=true := by decide +kernel
theorem fusedMap0517_checked : acceptsGraphIso
    (fused (graph core0517) (root 7) 1 1) DegreeOneSmallSpectrum380.graph fusedMap0517=true := by decide +kernel
theorem certified0517 : Certified (graph core0517) (root 7) 1 1 :=
  of_native_maps core0517 DegreeOneSmallSpectrum512.graph DegreeOneSmallSpectrum380.graph
    sourceMap0517 fusedMap0517 sourceMap0517_checked fusedMap0517_checked
    DegreeOneSmallComparisons.comparison0517
#print axioms sourceMap0517_checked
#print axioms fusedMap0517_checked
#print axioms certified0517
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
