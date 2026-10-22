/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0626 : Family 10 := level10.get ⟨770,by decide⟩
def sourceMap0626 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0626 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0626_checked : acceptsGraphIso
    (source (graph core0626) (root 10) 0 0) DegreeOneSmallSpectrum1688.graph sourceMap0626=true := by decide +kernel
theorem fusedMap0626_checked : acceptsGraphIso
    (fused (graph core0626) (root 10) 0 0) DegreeOneSmallSpectrum1401.graph fusedMap0626=true := by decide +kernel
theorem certified0626 : Certified (graph core0626) (root 10) 0 0 :=
  of_native_maps core0626 DegreeOneSmallSpectrum1688.graph DegreeOneSmallSpectrum1401.graph
    sourceMap0626 fusedMap0626 sourceMap0626_checked fusedMap0626_checked
    DegreeTwoThreeFiniteComparisons.comparison0626
#print axioms sourceMap0626_checked
#print axioms fusedMap0626_checked
#print axioms certified0626
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
