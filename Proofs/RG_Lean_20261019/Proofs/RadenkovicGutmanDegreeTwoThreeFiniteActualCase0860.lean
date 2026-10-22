/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0860 : Family 10 := level10.get ⟨1357,by decide⟩
def sourceMap0860 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0860 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0860_checked : acceptsGraphIso
    (source (graph core0860) (root 10) 0 0) DegreeOneSmallSpectrum1608.graph sourceMap0860=true := by decide +kernel
theorem fusedMap0860_checked : acceptsGraphIso
    (fused (graph core0860) (root 10) 0 0) DegreeOneSmallSpectrum1959.graph fusedMap0860=true := by decide +kernel
theorem certified0860 : Certified (graph core0860) (root 10) 0 0 :=
  of_native_maps core0860 DegreeOneSmallSpectrum1608.graph DegreeOneSmallSpectrum1959.graph
    sourceMap0860 fusedMap0860 sourceMap0860_checked fusedMap0860_checked
    DegreeTwoThreeFiniteComparisons.comparison0860
#print axioms sourceMap0860_checked
#print axioms fusedMap0860_checked
#print axioms certified0860
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
