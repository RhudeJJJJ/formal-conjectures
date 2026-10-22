/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0706 : Family 10 := level10.get ⟨970,by decide⟩
def sourceMap0706 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,8,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0706 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,8,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0706_checked : acceptsGraphIso
    (source (graph core0706) (root 10) 0 0) DegreeOneSmallSpectrum1017.graph sourceMap0706=true := by decide +kernel
theorem fusedMap0706_checked : acceptsGraphIso
    (fused (graph core0706) (root 10) 0 0) DegreeOneSmallSpectrum1011.graph fusedMap0706=true := by decide +kernel
theorem certified0706 : Certified (graph core0706) (root 10) 0 0 :=
  of_native_maps core0706 DegreeOneSmallSpectrum1017.graph DegreeOneSmallSpectrum1011.graph
    sourceMap0706 fusedMap0706 sourceMap0706_checked fusedMap0706_checked
    DegreeTwoThreeFiniteComparisons.comparison0706
#print axioms sourceMap0706_checked
#print axioms fusedMap0706_checked
#print axioms certified0706
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
