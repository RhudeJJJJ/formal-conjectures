/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0013 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap0013 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,2,3,4] (sourceLabel 6 0 0 v)
def fusedMap0013 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,4,2,3] (fusedLabel 6 0 0 v)
theorem sourceMap0013_checked : acceptsGraphIso
    (source (graph core0013) (root 6) 0 0) DegreeOneSmallSpectrum041.graph sourceMap0013=true := by decide +kernel
theorem fusedMap0013_checked : acceptsGraphIso
    (fused (graph core0013) (root 6) 0 0) DegreeOneSmallSpectrum059.graph fusedMap0013=true := by decide +kernel
theorem certified0013 : Certified (graph core0013) (root 6) 0 0 :=
  of_native_maps core0013 DegreeOneSmallSpectrum041.graph DegreeOneSmallSpectrum059.graph
    sourceMap0013 fusedMap0013 sourceMap0013_checked fusedMap0013_checked
    DegreeTwoThreeFiniteComparisons.comparison0013
#print axioms sourceMap0013_checked
#print axioms fusedMap0013_checked
#print axioms certified0013
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
