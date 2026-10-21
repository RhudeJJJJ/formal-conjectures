/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0645 : Family 7 := level7.get ⟨50,by decide⟩
def sourceMap0645 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (sourceLabel 7 0 0 v)
def fusedMap0645 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,4,5,6,7,8,9,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap0645_checked : acceptsGraphIso
    (source (graph core0645) (root 7) 0 0) DegreeOneSmallSpectrum147.graph sourceMap0645=true := by decide +kernel
theorem fusedMap0645_checked : acceptsGraphIso
    (fused (graph core0645) (root 7) 0 0) DegreeOneSmallSpectrum146.graph fusedMap0645=true := by decide +kernel
theorem certified0645 : Certified (graph core0645) (root 7) 0 0 :=
  of_native_maps core0645 DegreeOneSmallSpectrum147.graph DegreeOneSmallSpectrum146.graph
    sourceMap0645 fusedMap0645 sourceMap0645_checked fusedMap0645_checked
    DegreeOneSmallComparisons.comparison0645
#print axioms sourceMap0645_checked
#print axioms fusedMap0645_checked
#print axioms certified0645
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
