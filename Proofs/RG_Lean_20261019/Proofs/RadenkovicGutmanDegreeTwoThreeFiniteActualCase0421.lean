/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0421 : Family 10 := level10.get ⟨117,by decide⟩
def sourceMap0421 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0421 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0421_checked : acceptsGraphIso
    (source (graph core0421) (root 10) 0 0) DegreeOneSmallSpectrum919.graph sourceMap0421=true := by decide +kernel
theorem fusedMap0421_checked : acceptsGraphIso
    (fused (graph core0421) (root 10) 0 0) DegreeOneSmallSpectrum912.graph fusedMap0421=true := by decide +kernel
theorem certified0421 : Certified (graph core0421) (root 10) 0 0 :=
  of_native_maps core0421 DegreeOneSmallSpectrum919.graph DegreeOneSmallSpectrum912.graph
    sourceMap0421 fusedMap0421 sourceMap0421_checked fusedMap0421_checked
    DegreeTwoThreeFiniteComparisons.comparison0421
#print axioms sourceMap0421_checked
#print axioms fusedMap0421_checked
#print axioms certified0421
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
