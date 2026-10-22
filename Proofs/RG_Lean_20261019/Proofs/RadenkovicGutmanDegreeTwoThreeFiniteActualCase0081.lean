/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0081 : Family 8 := level8.get ⟨74,by decide⟩
def sourceMap0081 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0081 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0081_checked : acceptsGraphIso
    (source (graph core0081) (root 8) 0 0) DegreeOneSmallSpectrum265.graph sourceMap0081=true := by decide +kernel
theorem fusedMap0081_checked : acceptsGraphIso
    (fused (graph core0081) (root 8) 0 0) DegreeOneSmallSpectrum214.graph fusedMap0081=true := by decide +kernel
theorem certified0081 : Certified (graph core0081) (root 8) 0 0 :=
  of_native_maps core0081 DegreeOneSmallSpectrum265.graph DegreeOneSmallSpectrum214.graph
    sourceMap0081 fusedMap0081 sourceMap0081_checked fusedMap0081_checked
    DegreeTwoThreeFiniteComparisons.comparison0081
#print axioms sourceMap0081_checked
#print axioms fusedMap0081_checked
#print axioms certified0081
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
