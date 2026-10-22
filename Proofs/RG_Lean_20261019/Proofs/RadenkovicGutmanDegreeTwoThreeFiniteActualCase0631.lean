/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0631 : Family 10 := level10.get ⟨785,by decide⟩
def sourceMap0631 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0631 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0631_checked : acceptsGraphIso
    (source (graph core0631) (root 10) 0 0) DegreeOneSmallSpectrum1665.graph sourceMap0631=true := by decide +kernel
theorem fusedMap0631_checked : acceptsGraphIso
    (fused (graph core0631) (root 10) 0 0) DegreeOneSmallSpectrum1419.graph fusedMap0631=true := by decide +kernel
theorem certified0631 : Certified (graph core0631) (root 10) 0 0 :=
  of_native_maps core0631 DegreeOneSmallSpectrum1665.graph DegreeOneSmallSpectrum1419.graph
    sourceMap0631 fusedMap0631 sourceMap0631_checked fusedMap0631_checked
    DegreeTwoThreeFiniteComparisons.comparison0631
#print axioms sourceMap0631_checked
#print axioms fusedMap0631_checked
#print axioms certified0631
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
