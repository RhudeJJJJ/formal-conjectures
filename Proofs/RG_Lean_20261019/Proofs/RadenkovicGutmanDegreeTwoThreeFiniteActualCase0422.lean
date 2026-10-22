/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0422 : Family 10 := level10.get ⟨125,by decide⟩
def sourceMap0422 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0422 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0422_checked : acceptsGraphIso
    (source (graph core0422) (root 10) 0 0) DegreeOneSmallSpectrum1077.graph sourceMap0422=true := by decide +kernel
theorem fusedMap0422_checked : acceptsGraphIso
    (fused (graph core0422) (root 10) 0 0) DegreeOneSmallSpectrum937.graph fusedMap0422=true := by decide +kernel
theorem certified0422 : Certified (graph core0422) (root 10) 0 0 :=
  of_native_maps core0422 DegreeOneSmallSpectrum1077.graph DegreeOneSmallSpectrum937.graph
    sourceMap0422 fusedMap0422 sourceMap0422_checked fusedMap0422_checked
    DegreeTwoThreeFiniteComparisons.comparison0422
#print axioms sourceMap0422_checked
#print axioms fusedMap0422_checked
#print axioms certified0422
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
