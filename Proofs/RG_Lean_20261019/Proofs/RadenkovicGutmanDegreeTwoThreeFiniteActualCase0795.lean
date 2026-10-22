/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0795 : Family 10 := level10.get ⟨1200,by decide⟩
def sourceMap0795 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0795 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0795_checked : acceptsGraphIso
    (source (graph core0795) (root 10) 0 0) DegreeOneSmallSpectrum1209.graph sourceMap0795=true := by decide +kernel
theorem fusedMap0795_checked : acceptsGraphIso
    (fused (graph core0795) (root 10) 0 0) DegreeOneSmallSpectrum1208.graph fusedMap0795=true := by decide +kernel
theorem certified0795 : Certified (graph core0795) (root 10) 0 0 :=
  of_native_maps core0795 DegreeOneSmallSpectrum1209.graph DegreeOneSmallSpectrum1208.graph
    sourceMap0795 fusedMap0795 sourceMap0795_checked fusedMap0795_checked
    DegreeTwoThreeFiniteComparisons.comparison0795
#print axioms sourceMap0795_checked
#print axioms fusedMap0795_checked
#print axioms certified0795
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
