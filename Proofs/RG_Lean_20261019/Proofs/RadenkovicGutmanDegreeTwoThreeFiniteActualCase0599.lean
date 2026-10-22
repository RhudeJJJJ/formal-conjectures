/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0599 : Family 10 := level10.get ⟨690,by decide⟩
def sourceMap0599 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0599 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0599_checked : acceptsGraphIso
    (source (graph core0599) (root 10) 0 0) DegreeTwoThreeSpectrum1461.graph sourceMap0599=true := by decide +kernel
theorem fusedMap0599_checked : acceptsGraphIso
    (fused (graph core0599) (root 10) 0 0) DegreeOneSmallSpectrum1299.graph fusedMap0599=true := by decide +kernel
theorem certified0599 : Certified (graph core0599) (root 10) 0 0 :=
  of_native_maps core0599 DegreeTwoThreeSpectrum1461.graph DegreeOneSmallSpectrum1299.graph
    sourceMap0599 fusedMap0599 sourceMap0599_checked fusedMap0599_checked
    DegreeTwoThreeFiniteComparisons.comparison0599
#print axioms sourceMap0599_checked
#print axioms fusedMap0599_checked
#print axioms certified0599
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
