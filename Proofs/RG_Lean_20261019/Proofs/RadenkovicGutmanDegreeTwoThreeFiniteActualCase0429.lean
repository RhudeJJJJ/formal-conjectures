/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0429 : Family 10 := level10.get ⟨154,by decide⟩
def sourceMap0429 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0429 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0429_checked : acceptsGraphIso
    (source (graph core0429) (root 10) 0 0) DegreeOneSmallSpectrum1082.graph sourceMap0429=true := by decide +kernel
theorem fusedMap0429_checked : acceptsGraphIso
    (fused (graph core0429) (root 10) 0 0) DegreeOneSmallSpectrum942.graph fusedMap0429=true := by decide +kernel
theorem certified0429 : Certified (graph core0429) (root 10) 0 0 :=
  of_native_maps core0429 DegreeOneSmallSpectrum1082.graph DegreeOneSmallSpectrum942.graph
    sourceMap0429 fusedMap0429 sourceMap0429_checked fusedMap0429_checked
    DegreeTwoThreeFiniteComparisons.comparison0429
#print axioms sourceMap0429_checked
#print axioms fusedMap0429_checked
#print axioms certified0429
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
