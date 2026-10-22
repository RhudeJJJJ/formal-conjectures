/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0678 : Family 10 := level10.get ⟨909,by decide⟩
def sourceMap0678 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0678 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0678_checked : acceptsGraphIso
    (source (graph core0678) (root 10) 0 0) DegreeOneSmallSpectrum1646.graph sourceMap0678=true := by decide +kernel
theorem fusedMap0678_checked : acceptsGraphIso
    (fused (graph core0678) (root 10) 0 0) DegreeOneSmallSpectrum1417.graph fusedMap0678=true := by decide +kernel
theorem certified0678 : Certified (graph core0678) (root 10) 0 0 :=
  of_native_maps core0678 DegreeOneSmallSpectrum1646.graph DegreeOneSmallSpectrum1417.graph
    sourceMap0678 fusedMap0678 sourceMap0678_checked fusedMap0678_checked
    DegreeTwoThreeFiniteComparisons.comparison0678
#print axioms sourceMap0678_checked
#print axioms fusedMap0678_checked
#print axioms certified0678
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
