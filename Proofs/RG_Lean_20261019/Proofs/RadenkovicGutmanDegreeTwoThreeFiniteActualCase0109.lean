/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0109 : Family 8 := level8.get ⟨152,by decide⟩
def sourceMap0109 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,5,6,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0109 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0109_checked : acceptsGraphIso
    (source (graph core0109) (root 8) 0 0) DegreeOneSmallSpectrum248.graph sourceMap0109=true := by decide +kernel
theorem fusedMap0109_checked : acceptsGraphIso
    (fused (graph core0109) (root 8) 0 0) DegreeOneSmallSpectrum339.graph fusedMap0109=true := by decide +kernel
theorem certified0109 : Certified (graph core0109) (root 8) 0 0 :=
  of_native_maps core0109 DegreeOneSmallSpectrum248.graph DegreeOneSmallSpectrum339.graph
    sourceMap0109 fusedMap0109 sourceMap0109_checked fusedMap0109_checked
    DegreeTwoThreeFiniteComparisons.comparison0109
#print axioms sourceMap0109_checked
#print axioms fusedMap0109_checked
#print axioms certified0109
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
