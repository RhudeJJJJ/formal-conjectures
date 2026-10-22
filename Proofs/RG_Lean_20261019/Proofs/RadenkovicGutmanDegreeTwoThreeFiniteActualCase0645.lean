/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0645 : Family 10 := level10.get ⟨818,by decide⟩
def sourceMap0645 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,7,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0645 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,7,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0645_checked : acceptsGraphIso
    (source (graph core0645) (root 10) 0 0) DegreeOneSmallSpectrum1122.graph sourceMap0645=true := by decide +kernel
theorem fusedMap0645_checked : acceptsGraphIso
    (fused (graph core0645) (root 10) 0 0) DegreeOneSmallSpectrum1099.graph fusedMap0645=true := by decide +kernel
theorem certified0645 : Certified (graph core0645) (root 10) 0 0 :=
  of_native_maps core0645 DegreeOneSmallSpectrum1122.graph DegreeOneSmallSpectrum1099.graph
    sourceMap0645 fusedMap0645 sourceMap0645_checked fusedMap0645_checked
    DegreeTwoThreeFiniteComparisons.comparison0645
#print axioms sourceMap0645_checked
#print axioms fusedMap0645_checked
#print axioms certified0645
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
