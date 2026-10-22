/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0400 : Family 10 := level10.get ⟨17,by decide⟩
def sourceMap0400 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0400 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0400_checked : acceptsGraphIso
    (source (graph core0400) (root 10) 0 0) DegreeOneSmallSpectrum866.graph sourceMap0400=true := by decide +kernel
theorem fusedMap0400_checked : acceptsGraphIso
    (fused (graph core0400) (root 10) 0 0) DegreeOneSmallSpectrum900.graph fusedMap0400=true := by decide +kernel
theorem certified0400 : Certified (graph core0400) (root 10) 0 0 :=
  of_native_maps core0400 DegreeOneSmallSpectrum866.graph DegreeOneSmallSpectrum900.graph
    sourceMap0400 fusedMap0400 sourceMap0400_checked fusedMap0400_checked
    DegreeTwoThreeFiniteComparisons.comparison0400
#print axioms sourceMap0400_checked
#print axioms fusedMap0400_checked
#print axioms certified0400
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
