/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0407 : Family 10 := level10.get ⟨51,by decide⟩
def sourceMap0407 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0407 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0407_checked : acceptsGraphIso
    (source (graph core0407) (root 10) 0 0) DegreeOneSmallSpectrum922.graph sourceMap0407=true := by decide +kernel
theorem fusedMap0407_checked : acceptsGraphIso
    (fused (graph core0407) (root 10) 0 0) DegreeOneSmallSpectrum915.graph fusedMap0407=true := by decide +kernel
theorem certified0407 : Certified (graph core0407) (root 10) 0 0 :=
  of_native_maps core0407 DegreeOneSmallSpectrum922.graph DegreeOneSmallSpectrum915.graph
    sourceMap0407 fusedMap0407 sourceMap0407_checked fusedMap0407_checked
    DegreeTwoThreeFiniteComparisons.comparison0407
#print axioms sourceMap0407_checked
#print axioms fusedMap0407_checked
#print axioms certified0407
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
