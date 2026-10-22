/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0988 : Family 10 := level10.get ⟨1669,by decide⟩
def sourceMap0988 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0988 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0988_checked : acceptsGraphIso
    (source (graph core0988) (root 10) 0 0) DegreeOneSmallSpectrum1573.graph sourceMap0988=true := by decide +kernel
theorem fusedMap0988_checked : acceptsGraphIso
    (fused (graph core0988) (root 10) 0 0) DegreeOneSmallSpectrum1564.graph fusedMap0988=true := by decide +kernel
theorem certified0988 : Certified (graph core0988) (root 10) 0 0 :=
  of_native_maps core0988 DegreeOneSmallSpectrum1573.graph DegreeOneSmallSpectrum1564.graph
    sourceMap0988 fusedMap0988 sourceMap0988_checked fusedMap0988_checked
    DegreeTwoThreeFiniteComparisons.comparison0988
#print axioms sourceMap0988_checked
#print axioms fusedMap0988_checked
#print axioms certified0988
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
