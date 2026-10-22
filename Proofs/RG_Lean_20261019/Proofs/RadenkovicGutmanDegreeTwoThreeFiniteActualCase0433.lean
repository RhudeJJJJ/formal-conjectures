/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0433 : Family 10 := level10.get ⟨168,by decide⟩
def sourceMap0433 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,9,10,11,12,7,8,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0433 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0433_checked : acceptsGraphIso
    (source (graph core0433) (root 10) 0 0) DegreeOneSmallSpectrum1044.graph sourceMap0433=true := by decide +kernel
theorem fusedMap0433_checked : acceptsGraphIso
    (fused (graph core0433) (root 10) 0 0) DegreeOneSmallSpectrum930.graph fusedMap0433=true := by decide +kernel
theorem certified0433 : Certified (graph core0433) (root 10) 0 0 :=
  of_native_maps core0433 DegreeOneSmallSpectrum1044.graph DegreeOneSmallSpectrum930.graph
    sourceMap0433 fusedMap0433 sourceMap0433_checked fusedMap0433_checked
    DegreeTwoThreeFiniteComparisons.comparison0433
#print axioms sourceMap0433_checked
#print axioms fusedMap0433_checked
#print axioms certified0433
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
