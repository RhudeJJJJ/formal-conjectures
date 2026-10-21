/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0779 : Family 8 := level8.get ⟨12,by decide⟩
def sourceMap0779 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 8 0 0 v)
def fusedMap0779 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0779_checked : acceptsGraphIso
    (source (graph core0779) (root 8) 0 0) DegreeOneSmallSpectrum179.graph sourceMap0779=true := by decide +kernel
theorem fusedMap0779_checked : acceptsGraphIso
    (fused (graph core0779) (root 8) 0 0) DegreeOneSmallSpectrum196.graph fusedMap0779=true := by decide +kernel
theorem certified0779 : Certified (graph core0779) (root 8) 0 0 :=
  of_native_maps core0779 DegreeOneSmallSpectrum179.graph DegreeOneSmallSpectrum196.graph
    sourceMap0779 fusedMap0779 sourceMap0779_checked fusedMap0779_checked
    DegreeOneSmallComparisons.comparison0779
#print axioms sourceMap0779_checked
#print axioms fusedMap0779_checked
#print axioms certified0779
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
