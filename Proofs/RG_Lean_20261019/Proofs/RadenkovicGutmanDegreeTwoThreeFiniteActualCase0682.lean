/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0682 : Family 10 := level10.get ⟨916,by decide⟩
def sourceMap0682 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0682 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0682_checked : acceptsGraphIso
    (source (graph core0682) (root 10) 0 0) DegreeOneSmallSpectrum964.graph sourceMap0682=true := by decide +kernel
theorem fusedMap0682_checked : acceptsGraphIso
    (fused (graph core0682) (root 10) 0 0) DegreeOneSmallSpectrum963.graph fusedMap0682=true := by decide +kernel
theorem certified0682 : Certified (graph core0682) (root 10) 0 0 :=
  of_native_maps core0682 DegreeOneSmallSpectrum964.graph DegreeOneSmallSpectrum963.graph
    sourceMap0682 fusedMap0682 sourceMap0682_checked fusedMap0682_checked
    DegreeTwoThreeFiniteComparisons.comparison0682
#print axioms sourceMap0682_checked
#print axioms fusedMap0682_checked
#print axioms certified0682
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
