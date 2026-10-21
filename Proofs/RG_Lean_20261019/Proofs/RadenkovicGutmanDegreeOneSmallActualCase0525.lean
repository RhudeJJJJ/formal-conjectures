/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0525 : Family 7 := level7.get ⟨15,by decide⟩
def sourceMap0525 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,6,7,8,9,5,3,4] (sourceLabel 7 0 0 v)
def fusedMap0525 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,5,0,1,2,3,4,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0525_checked : acceptsGraphIso
    (source (graph core0525) (root 7) 0 0) DegreeOneSmallSpectrum120.graph sourceMap0525=true := by decide +kernel
theorem fusedMap0525_checked : acceptsGraphIso
    (fused (graph core0525) (root 7) 0 0) DegreeOneSmallSpectrum085.graph fusedMap0525=true := by decide +kernel
theorem certified0525 : Certified (graph core0525) (root 7) 0 0 :=
  of_native_maps core0525 DegreeOneSmallSpectrum120.graph DegreeOneSmallSpectrum085.graph
    sourceMap0525 fusedMap0525 sourceMap0525_checked fusedMap0525_checked
    DegreeOneSmallComparisons.comparison0525
#print axioms sourceMap0525_checked
#print axioms fusedMap0525_checked
#print axioms certified0525
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
