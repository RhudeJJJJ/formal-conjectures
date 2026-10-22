/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0279 : Family 9 := level9.get ⟨383,by decide⟩
def sourceMap0279 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0279 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0279_checked : acceptsGraphIso
    (source (graph core0279) (root 9) 0 0) DegreeOneSmallSpectrum720.graph sourceMap0279=true := by decide +kernel
theorem fusedMap0279_checked : acceptsGraphIso
    (fused (graph core0279) (root 9) 0 0) DegreeOneSmallSpectrum700.graph fusedMap0279=true := by decide +kernel
theorem certified0279 : Certified (graph core0279) (root 9) 0 0 :=
  of_native_maps core0279 DegreeOneSmallSpectrum720.graph DegreeOneSmallSpectrum700.graph
    sourceMap0279 fusedMap0279 sourceMap0279_checked fusedMap0279_checked
    DegreeTwoThreeFiniteComparisons.comparison0279
#print axioms sourceMap0279_checked
#print axioms fusedMap0279_checked
#print axioms certified0279
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
