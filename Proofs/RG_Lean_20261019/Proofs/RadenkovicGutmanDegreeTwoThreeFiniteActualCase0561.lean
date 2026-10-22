/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0561 : Family 10 := level10.get ⟨584,by decide⟩
def sourceMap0561 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0561 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0561_checked : acceptsGraphIso
    (source (graph core0561) (root 10) 0 0) DegreeOneSmallSpectrum1678.graph sourceMap0561=true := by decide +kernel
theorem fusedMap0561_checked : acceptsGraphIso
    (fused (graph core0561) (root 10) 0 0) DegreeOneSmallSpectrum1122.graph fusedMap0561=true := by decide +kernel
theorem certified0561 : Certified (graph core0561) (root 10) 0 0 :=
  of_native_maps core0561 DegreeOneSmallSpectrum1678.graph DegreeOneSmallSpectrum1122.graph
    sourceMap0561 fusedMap0561 sourceMap0561_checked fusedMap0561_checked
    DegreeTwoThreeFiniteComparisons.comparison0561
#print axioms sourceMap0561_checked
#print axioms fusedMap0561_checked
#print axioms certified0561
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
