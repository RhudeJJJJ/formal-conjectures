/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0843 : Family 10 := level10.get ⟨1314,by decide⟩
def sourceMap0843 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0843 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0843_checked : acceptsGraphIso
    (source (graph core0843) (root 10) 0 0) DegreeOneSmallSpectrum1803.graph sourceMap0843=true := by decide +kernel
theorem fusedMap0843_checked : acceptsGraphIso
    (fused (graph core0843) (root 10) 0 0) DegreeOneSmallSpectrum1766.graph fusedMap0843=true := by decide +kernel
theorem certified0843 : Certified (graph core0843) (root 10) 0 0 :=
  of_native_maps core0843 DegreeOneSmallSpectrum1803.graph DegreeOneSmallSpectrum1766.graph
    sourceMap0843 fusedMap0843 sourceMap0843_checked fusedMap0843_checked
    DegreeTwoThreeFiniteComparisons.comparison0843
#print axioms sourceMap0843_checked
#print axioms fusedMap0843_checked
#print axioms certified0843
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
