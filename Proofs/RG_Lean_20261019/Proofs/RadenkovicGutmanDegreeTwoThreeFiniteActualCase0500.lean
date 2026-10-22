/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0500 : Family 10 := level10.get ⟨400,by decide⟩
def sourceMap0500 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0500 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0500_checked : acceptsGraphIso
    (source (graph core0500) (root 10) 0 0) DegreeOneSmallSpectrum1035.graph sourceMap0500=true := by decide +kernel
theorem fusedMap0500_checked : acceptsGraphIso
    (fused (graph core0500) (root 10) 0 0) DegreeOneSmallSpectrum1432.graph fusedMap0500=true := by decide +kernel
theorem certified0500 : Certified (graph core0500) (root 10) 0 0 :=
  of_native_maps core0500 DegreeOneSmallSpectrum1035.graph DegreeOneSmallSpectrum1432.graph
    sourceMap0500 fusedMap0500 sourceMap0500_checked fusedMap0500_checked
    DegreeTwoThreeFiniteComparisons.comparison0500
#print axioms sourceMap0500_checked
#print axioms fusedMap0500_checked
#print axioms certified0500
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
