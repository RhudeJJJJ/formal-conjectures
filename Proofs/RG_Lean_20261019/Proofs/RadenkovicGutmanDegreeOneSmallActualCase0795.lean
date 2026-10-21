/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0795 : Family 8 := level8.get ⟨17,by decide⟩
def sourceMap0795 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 8 0 0 v)
def fusedMap0795 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0795_checked : acceptsGraphIso
    (source (graph core0795) (root 8) 0 0) DegreeOneSmallSpectrum186.graph sourceMap0795=true := by decide +kernel
theorem fusedMap0795_checked : acceptsGraphIso
    (fused (graph core0795) (root 8) 0 0) DegreeOneSmallSpectrum217.graph fusedMap0795=true := by decide +kernel
theorem certified0795 : Certified (graph core0795) (root 8) 0 0 :=
  of_native_maps core0795 DegreeOneSmallSpectrum186.graph DegreeOneSmallSpectrum217.graph
    sourceMap0795 fusedMap0795 sourceMap0795_checked fusedMap0795_checked
    DegreeOneSmallComparisons.comparison0795
#print axioms sourceMap0795_checked
#print axioms fusedMap0795_checked
#print axioms certified0795
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
