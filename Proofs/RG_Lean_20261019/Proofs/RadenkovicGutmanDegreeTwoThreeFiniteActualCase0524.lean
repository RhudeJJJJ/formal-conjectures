/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0524 : Family 10 := level10.get ⟨471,by decide⟩
def sourceMap0524 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,1,0,9,10,11,12,2,3,4,6,7,8] (sourceLabel 10 0 0 v)
def fusedMap0524 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0524_checked : acceptsGraphIso
    (source (graph core0524) (root 10) 0 0) DegreeOneSmallSpectrum1467.graph sourceMap0524=true := by decide +kernel
theorem fusedMap0524_checked : acceptsGraphIso
    (fused (graph core0524) (root 10) 0 0) DegreeOneSmallSpectrum1398.graph fusedMap0524=true := by decide +kernel
theorem certified0524 : Certified (graph core0524) (root 10) 0 0 :=
  of_native_maps core0524 DegreeOneSmallSpectrum1467.graph DegreeOneSmallSpectrum1398.graph
    sourceMap0524 fusedMap0524 sourceMap0524_checked fusedMap0524_checked
    DegreeTwoThreeFiniteComparisons.comparison0524
#print axioms sourceMap0524_checked
#print axioms fusedMap0524_checked
#print axioms certified0524
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
