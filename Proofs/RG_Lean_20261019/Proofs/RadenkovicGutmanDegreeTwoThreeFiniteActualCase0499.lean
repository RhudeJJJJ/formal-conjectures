/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0499 : Family 10 := level10.get ⟨397,by decide⟩
def sourceMap0499 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0499 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0499_checked : acceptsGraphIso
    (source (graph core0499) (root 10) 0 0) DegreeOneSmallSpectrum1057.graph sourceMap0499=true := by decide +kernel
theorem fusedMap0499_checked : acceptsGraphIso
    (fused (graph core0499) (root 10) 0 0) DegreeOneSmallSpectrum1449.graph fusedMap0499=true := by decide +kernel
theorem certified0499 : Certified (graph core0499) (root 10) 0 0 :=
  of_native_maps core0499 DegreeOneSmallSpectrum1057.graph DegreeOneSmallSpectrum1449.graph
    sourceMap0499 fusedMap0499 sourceMap0499_checked fusedMap0499_checked
    DegreeTwoThreeFiniteComparisons.comparison0499
#print axioms sourceMap0499_checked
#print axioms fusedMap0499_checked
#print axioms certified0499
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
