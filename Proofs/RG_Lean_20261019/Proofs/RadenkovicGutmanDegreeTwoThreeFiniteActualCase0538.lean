/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0538 : Family 10 := level10.get ⟨510,by decide⟩
def sourceMap0538 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0538 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0538_checked : acceptsGraphIso
    (source (graph core0538) (root 10) 0 0) DegreeTwoThreeSpectrum1340.graph sourceMap0538=true := by decide +kernel
theorem fusedMap0538_checked : acceptsGraphIso
    (fused (graph core0538) (root 10) 0 0) DegreeOneSmallSpectrum996.graph fusedMap0538=true := by decide +kernel
theorem certified0538 : Certified (graph core0538) (root 10) 0 0 :=
  of_native_maps core0538 DegreeTwoThreeSpectrum1340.graph DegreeOneSmallSpectrum996.graph
    sourceMap0538 fusedMap0538 sourceMap0538_checked fusedMap0538_checked
    DegreeTwoThreeFiniteComparisons.comparison0538
#print axioms sourceMap0538_checked
#print axioms fusedMap0538_checked
#print axioms certified0538
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
