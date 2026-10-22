/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0560 : Family 10 := level10.get ⟨580,by decide⟩
def sourceMap0560 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0560 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0560_checked : acceptsGraphIso
    (source (graph core0560) (root 10) 0 0) DegreeOneSmallSpectrum1677.graph sourceMap0560=true := by decide +kernel
theorem fusedMap0560_checked : acceptsGraphIso
    (fused (graph core0560) (root 10) 0 0) DegreeOneSmallSpectrum1116.graph fusedMap0560=true := by decide +kernel
theorem certified0560 : Certified (graph core0560) (root 10) 0 0 :=
  of_native_maps core0560 DegreeOneSmallSpectrum1677.graph DegreeOneSmallSpectrum1116.graph
    sourceMap0560 fusedMap0560 sourceMap0560_checked fusedMap0560_checked
    DegreeTwoThreeFiniteComparisons.comparison0560
#print axioms sourceMap0560_checked
#print axioms fusedMap0560_checked
#print axioms certified0560
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
