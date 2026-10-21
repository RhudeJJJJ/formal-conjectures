/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0481 : Family 7 := level7.get ⟨5,by decide⟩
def sourceMap0481 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,7,3,4,5,6] (sourceLabel 7 1 1 v)
def fusedMap0481 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 7 1 1 v)
theorem sourceMap0481_checked : acceptsGraphIso
    (source (graph core0481) (root 7) 1 1) DegreeOneSmallSpectrum510.graph sourceMap0481=true := by decide +kernel
theorem fusedMap0481_checked : acceptsGraphIso
    (fused (graph core0481) (root 7) 1 1) DegreeOneSmallSpectrum397.graph fusedMap0481=true := by decide +kernel
theorem certified0481 : Certified (graph core0481) (root 7) 1 1 :=
  of_native_maps core0481 DegreeOneSmallSpectrum510.graph DegreeOneSmallSpectrum397.graph
    sourceMap0481 fusedMap0481 sourceMap0481_checked fusedMap0481_checked
    DegreeOneSmallComparisons.comparison0481
#print axioms sourceMap0481_checked
#print axioms fusedMap0481_checked
#print axioms certified0481
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
