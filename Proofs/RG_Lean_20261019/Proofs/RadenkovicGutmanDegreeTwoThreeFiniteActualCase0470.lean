/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0470 : Family 10 := level10.get ⟨298,by decide⟩
def sourceMap0470 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0470 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0470_checked : acceptsGraphIso
    (source (graph core0470) (root 10) 0 0) DegreeOneSmallSpectrum1053.graph sourceMap0470=true := by decide +kernel
theorem fusedMap0470_checked : acceptsGraphIso
    (fused (graph core0470) (root 10) 0 0) DegreeOneSmallSpectrum1339.graph fusedMap0470=true := by decide +kernel
theorem certified0470 : Certified (graph core0470) (root 10) 0 0 :=
  of_native_maps core0470 DegreeOneSmallSpectrum1053.graph DegreeOneSmallSpectrum1339.graph
    sourceMap0470 fusedMap0470 sourceMap0470_checked fusedMap0470_checked
    DegreeTwoThreeFiniteComparisons.comparison0470
#print axioms sourceMap0470_checked
#print axioms fusedMap0470_checked
#print axioms certified0470
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
