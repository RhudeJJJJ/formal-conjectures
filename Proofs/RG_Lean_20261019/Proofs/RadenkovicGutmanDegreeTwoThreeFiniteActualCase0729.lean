/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0729 : Family 10 := level10.get ⟨1035,by decide⟩
def sourceMap0729 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0729 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0729_checked : acceptsGraphIso
    (source (graph core0729) (root 10) 0 0) DegreeOneSmallSpectrum1610.graph sourceMap0729=true := by decide +kernel
theorem fusedMap0729_checked : acceptsGraphIso
    (fused (graph core0729) (root 10) 0 0) DegreeOneSmallSpectrum1615.graph fusedMap0729=true := by decide +kernel
theorem certified0729 : Certified (graph core0729) (root 10) 0 0 :=
  of_native_maps core0729 DegreeOneSmallSpectrum1610.graph DegreeOneSmallSpectrum1615.graph
    sourceMap0729 fusedMap0729 sourceMap0729_checked fusedMap0729_checked
    DegreeTwoThreeFiniteComparisons.comparison0729
#print axioms sourceMap0729_checked
#print axioms fusedMap0729_checked
#print axioms certified0729
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
