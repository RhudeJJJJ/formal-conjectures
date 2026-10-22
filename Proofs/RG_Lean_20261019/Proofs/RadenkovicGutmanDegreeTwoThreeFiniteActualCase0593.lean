/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0593 : Family 10 := level10.get ⟨671,by decide⟩
def sourceMap0593 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,7,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0593 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,7,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0593_checked : acceptsGraphIso
    (source (graph core0593) (root 10) 0 0) DegreeOneSmallSpectrum1121.graph sourceMap0593=true := by decide +kernel
theorem fusedMap0593_checked : acceptsGraphIso
    (fused (graph core0593) (root 10) 0 0) DegreeOneSmallSpectrum1098.graph fusedMap0593=true := by decide +kernel
theorem certified0593 : Certified (graph core0593) (root 10) 0 0 :=
  of_native_maps core0593 DegreeOneSmallSpectrum1121.graph DegreeOneSmallSpectrum1098.graph
    sourceMap0593 fusedMap0593 sourceMap0593_checked fusedMap0593_checked
    DegreeTwoThreeFiniteComparisons.comparison0593
#print axioms sourceMap0593_checked
#print axioms fusedMap0593_checked
#print axioms certified0593
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
