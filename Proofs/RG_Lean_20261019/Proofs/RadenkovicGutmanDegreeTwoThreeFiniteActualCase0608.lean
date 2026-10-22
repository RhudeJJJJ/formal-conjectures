/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0608 : Family 10 := level10.get ⟨718,by decide⟩
def sourceMap0608 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0608 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0608_checked : acceptsGraphIso
    (source (graph core0608) (root 10) 0 0) DegreeOneSmallSpectrum1651.graph sourceMap0608=true := by decide +kernel
theorem fusedMap0608_checked : acceptsGraphIso
    (fused (graph core0608) (root 10) 0 0) DegreeOneSmallSpectrum1337.graph fusedMap0608=true := by decide +kernel
theorem certified0608 : Certified (graph core0608) (root 10) 0 0 :=
  of_native_maps core0608 DegreeOneSmallSpectrum1651.graph DegreeOneSmallSpectrum1337.graph
    sourceMap0608 fusedMap0608 sourceMap0608_checked fusedMap0608_checked
    DegreeTwoThreeFiniteComparisons.comparison0608
#print axioms sourceMap0608_checked
#print axioms fusedMap0608_checked
#print axioms certified0608
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
