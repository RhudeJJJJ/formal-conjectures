/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0504 : Family 10 := level10.get ⟨413,by decide⟩
def sourceMap0504 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0504 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0504_checked : acceptsGraphIso
    (source (graph core0504) (root 10) 0 0) DegreeOneSmallSpectrum1026.graph sourceMap0504=true := by decide +kernel
theorem fusedMap0504_checked : acceptsGraphIso
    (fused (graph core0504) (root 10) 0 0) DegreeOneSmallSpectrum1433.graph fusedMap0504=true := by decide +kernel
theorem certified0504 : Certified (graph core0504) (root 10) 0 0 :=
  of_native_maps core0504 DegreeOneSmallSpectrum1026.graph DegreeOneSmallSpectrum1433.graph
    sourceMap0504 fusedMap0504 sourceMap0504_checked fusedMap0504_checked
    DegreeTwoThreeFiniteComparisons.comparison0504
#print axioms sourceMap0504_checked
#print axioms fusedMap0504_checked
#print axioms certified0504
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
