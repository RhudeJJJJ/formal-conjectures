/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0362 : Family 6 := level6.get ⟨12,by decide⟩
def sourceMap0362 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 6 1 1 v)
def fusedMap0362 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0362_checked : acceptsGraphIso
    (source (graph core0362) (root 6) 1 1) DegreeOneSmallSpectrum328.graph sourceMap0362=true := by decide +kernel
theorem fusedMap0362_checked : acceptsGraphIso
    (fused (graph core0362) (root 6) 1 1) DegreeOneSmallSpectrum212.graph fusedMap0362=true := by decide +kernel
theorem certified0362 : Certified (graph core0362) (root 6) 1 1 :=
  of_native_maps core0362 DegreeOneSmallSpectrum328.graph DegreeOneSmallSpectrum212.graph
    sourceMap0362 fusedMap0362 sourceMap0362_checked fusedMap0362_checked
    DegreeOneSmallComparisons.comparison0362
#print axioms sourceMap0362_checked
#print axioms fusedMap0362_checked
#print axioms certified0362
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
