/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0657 : Family 10 := level10.get ⟨854,by decide⟩
def sourceMap0657 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0657 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0657_checked : acceptsGraphIso
    (source (graph core0657) (root 10) 0 0) DegreeOneSmallSpectrum1694.graph sourceMap0657=true := by decide +kernel
theorem fusedMap0657_checked : acceptsGraphIso
    (fused (graph core0657) (root 10) 0 0) DegreeOneSmallSpectrum1443.graph fusedMap0657=true := by decide +kernel
theorem certified0657 : Certified (graph core0657) (root 10) 0 0 :=
  of_native_maps core0657 DegreeOneSmallSpectrum1694.graph DegreeOneSmallSpectrum1443.graph
    sourceMap0657 fusedMap0657 sourceMap0657_checked fusedMap0657_checked
    DegreeTwoThreeFiniteComparisons.comparison0657
#print axioms sourceMap0657_checked
#print axioms fusedMap0657_checked
#print axioms certified0657
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
