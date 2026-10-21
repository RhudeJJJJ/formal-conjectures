/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0715 : Family 7 := level7.get ⟨81,by decide⟩
def sourceMap0715 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0715 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0715_checked : acceptsGraphIso
    (source (graph core0715) (root 7) 1 1) DegreeOneSmallSpectrum775.graph sourceMap0715=true := by decide +kernel
theorem fusedMap0715_checked : acceptsGraphIso
    (fused (graph core0715) (root 7) 1 1) DegreeOneSmallSpectrum500.graph fusedMap0715=true := by decide +kernel
theorem certified0715 : Certified (graph core0715) (root 7) 1 1 :=
  of_native_maps core0715 DegreeOneSmallSpectrum775.graph DegreeOneSmallSpectrum500.graph
    sourceMap0715 fusedMap0715 sourceMap0715_checked fusedMap0715_checked
    DegreeOneSmallComparisons.comparison0715
#print axioms sourceMap0715_checked
#print axioms fusedMap0715_checked
#print axioms certified0715
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
