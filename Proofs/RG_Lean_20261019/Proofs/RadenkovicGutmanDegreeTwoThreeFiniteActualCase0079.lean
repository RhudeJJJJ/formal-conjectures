/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0079 : Family 8 := level8.get ⟨67,by decide⟩
def sourceMap0079 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,6,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0079 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,4,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0079_checked : acceptsGraphIso
    (source (graph core0079) (root 8) 0 0) DegreeOneSmallSpectrum257.graph sourceMap0079=true := by decide +kernel
theorem fusedMap0079_checked : acceptsGraphIso
    (fused (graph core0079) (root 8) 0 0) DegreeOneSmallSpectrum210.graph fusedMap0079=true := by decide +kernel
theorem certified0079 : Certified (graph core0079) (root 8) 0 0 :=
  of_native_maps core0079 DegreeOneSmallSpectrum257.graph DegreeOneSmallSpectrum210.graph
    sourceMap0079 fusedMap0079 sourceMap0079_checked fusedMap0079_checked
    DegreeTwoThreeFiniteComparisons.comparison0079
#print axioms sourceMap0079_checked
#print axioms fusedMap0079_checked
#print axioms certified0079
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
