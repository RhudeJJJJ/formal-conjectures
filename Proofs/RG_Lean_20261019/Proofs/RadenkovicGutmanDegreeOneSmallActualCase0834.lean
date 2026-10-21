/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0834 : Family 8 := level8.get ⟨29,by decide⟩
def sourceMap0834 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,7,8,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0834 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 8 1 1 v)
theorem sourceMap0834_checked : acceptsGraphIso
    (source (graph core0834) (root 8) 1 1) DegreeOneSmallSpectrum1319.graph sourceMap0834=true := by decide +kernel
theorem fusedMap0834_checked : acceptsGraphIso
    (fused (graph core0834) (root 8) 1 1) DegreeOneSmallSpectrum977.graph fusedMap0834=true := by decide +kernel
theorem certified0834 : Certified (graph core0834) (root 8) 1 1 :=
  of_native_maps core0834 DegreeOneSmallSpectrum1319.graph DegreeOneSmallSpectrum977.graph
    sourceMap0834 fusedMap0834 sourceMap0834_checked fusedMap0834_checked
    DegreeOneSmallComparisons.comparison0834
#print axioms sourceMap0834_checked
#print axioms fusedMap0834_checked
#print axioms certified0834
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
