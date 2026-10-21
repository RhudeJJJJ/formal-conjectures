/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0607 : Family 7 := level7.get ⟨35,by decide⟩
def sourceMap0607 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,10,11,6,7,8,9] (sourceLabel 7 1 1 v)
def fusedMap0607 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0607_checked : acceptsGraphIso
    (source (graph core0607) (root 7) 1 1) DegreeOneSmallSpectrum755.graph sourceMap0607=true := by decide +kernel
theorem fusedMap0607_checked : acceptsGraphIso
    (fused (graph core0607) (root 7) 1 1) DegreeOneSmallSpectrum469.graph fusedMap0607=true := by decide +kernel
theorem certified0607 : Certified (graph core0607) (root 7) 1 1 :=
  of_native_maps core0607 DegreeOneSmallSpectrum755.graph DegreeOneSmallSpectrum469.graph
    sourceMap0607 fusedMap0607 sourceMap0607_checked fusedMap0607_checked
    DegreeOneSmallComparisons.comparison0607
#print axioms sourceMap0607_checked
#print axioms fusedMap0607_checked
#print axioms certified0607
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
