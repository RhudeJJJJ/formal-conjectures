/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0639 : Family 10 := level10.get ⟨807,by decide⟩
def sourceMap0639 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0639 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0639_checked : acceptsGraphIso
    (source (graph core0639) (root 10) 0 0) DegreeOneSmallSpectrum1615.graph sourceMap0639=true := by decide +kernel
theorem fusedMap0639_checked : acceptsGraphIso
    (fused (graph core0639) (root 10) 0 0) DegreeOneSmallSpectrum1401.graph fusedMap0639=true := by decide +kernel
theorem certified0639 : Certified (graph core0639) (root 10) 0 0 :=
  of_native_maps core0639 DegreeOneSmallSpectrum1615.graph DegreeOneSmallSpectrum1401.graph
    sourceMap0639 fusedMap0639 sourceMap0639_checked fusedMap0639_checked
    DegreeTwoThreeFiniteComparisons.comparison0639
#print axioms sourceMap0639_checked
#print axioms fusedMap0639_checked
#print axioms certified0639
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
