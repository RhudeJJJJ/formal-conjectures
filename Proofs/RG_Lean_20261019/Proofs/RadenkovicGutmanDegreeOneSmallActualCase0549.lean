/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0549 : Family 7 := level7.get ⟨21,by decide⟩
def sourceMap0549 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,7,8,9,5,6,3,4] (sourceLabel 7 0 0 v)
def fusedMap0549 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,4,5,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap0549_checked : acceptsGraphIso
    (source (graph core0549) (root 7) 0 0) DegreeOneSmallSpectrum111.graph sourceMap0549=true := by decide +kernel
theorem fusedMap0549_checked : acceptsGraphIso
    (fused (graph core0549) (root 7) 0 0) DegreeOneSmallSpectrum087.graph fusedMap0549=true := by decide +kernel
theorem certified0549 : Certified (graph core0549) (root 7) 0 0 :=
  of_native_maps core0549 DegreeOneSmallSpectrum111.graph DegreeOneSmallSpectrum087.graph
    sourceMap0549 fusedMap0549 sourceMap0549_checked fusedMap0549_checked
    DegreeOneSmallComparisons.comparison0549
#print axioms sourceMap0549_checked
#print axioms fusedMap0549_checked
#print axioms certified0549
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
