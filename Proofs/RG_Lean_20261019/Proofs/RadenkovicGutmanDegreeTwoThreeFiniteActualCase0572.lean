/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0572 : Family 10 := level10.get ⟨612,by decide⟩
def sourceMap0572 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0572 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0572_checked : acceptsGraphIso
    (source (graph core0572) (root 10) 0 0) DegreeOneSmallSpectrum1125.graph sourceMap0572=true := by decide +kernel
theorem fusedMap0572_checked : acceptsGraphIso
    (fused (graph core0572) (root 10) 0 0) DegreeOneSmallSpectrum1102.graph fusedMap0572=true := by decide +kernel
theorem certified0572 : Certified (graph core0572) (root 10) 0 0 :=
  of_native_maps core0572 DegreeOneSmallSpectrum1125.graph DegreeOneSmallSpectrum1102.graph
    sourceMap0572 fusedMap0572 sourceMap0572_checked fusedMap0572_checked
    DegreeTwoThreeFiniteComparisons.comparison0572
#print axioms sourceMap0572_checked
#print axioms fusedMap0572_checked
#print axioms certified0572
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
