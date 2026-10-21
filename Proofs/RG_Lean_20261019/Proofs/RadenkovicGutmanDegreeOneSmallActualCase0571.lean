/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0571 : Family 7 := level7.get ⟨27,by decide⟩
def sourceMap0571 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0571 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0571_checked : acceptsGraphIso
    (source (graph core0571) (root 7) 1 1) DegreeOneSmallSpectrum654.graph sourceMap0571=true := by decide +kernel
theorem fusedMap0571_checked : acceptsGraphIso
    (fused (graph core0571) (root 7) 1 1) DegreeOneSmallSpectrum411.graph fusedMap0571=true := by decide +kernel
theorem certified0571 : Certified (graph core0571) (root 7) 1 1 :=
  of_native_maps core0571 DegreeOneSmallSpectrum654.graph DegreeOneSmallSpectrum411.graph
    sourceMap0571 fusedMap0571 sourceMap0571_checked fusedMap0571_checked
    DegreeOneSmallComparisons.comparison0571
#print axioms sourceMap0571_checked
#print axioms fusedMap0571_checked
#print axioms certified0571
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
