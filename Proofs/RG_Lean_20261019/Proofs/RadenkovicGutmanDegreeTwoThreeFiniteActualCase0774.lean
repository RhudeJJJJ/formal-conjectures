/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0774 : Family 10 := level10.get ⟨1152,by decide⟩
def sourceMap0774 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0774 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0774_checked : acceptsGraphIso
    (source (graph core0774) (root 10) 0 0) DegreeOneSmallSpectrum1611.graph sourceMap0774=true := by decide +kernel
theorem fusedMap0774_checked : acceptsGraphIso
    (fused (graph core0774) (root 10) 0 0) DegreeOneSmallSpectrum1830.graph fusedMap0774=true := by decide +kernel
theorem certified0774 : Certified (graph core0774) (root 10) 0 0 :=
  of_native_maps core0774 DegreeOneSmallSpectrum1611.graph DegreeOneSmallSpectrum1830.graph
    sourceMap0774 fusedMap0774 sourceMap0774_checked fusedMap0774_checked
    DegreeTwoThreeFiniteComparisons.comparison0774
#print axioms sourceMap0774_checked
#print axioms fusedMap0774_checked
#print axioms certified0774
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
