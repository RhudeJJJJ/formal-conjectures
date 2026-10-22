/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0554 : Family 10 := level10.get ⟨556,by decide⟩
def sourceMap0554 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0554 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0554_checked : acceptsGraphIso
    (source (graph core0554) (root 10) 0 0) DegreeOneSmallSpectrum1061.graph sourceMap0554=true := by decide +kernel
theorem fusedMap0554_checked : acceptsGraphIso
    (fused (graph core0554) (root 10) 0 0) DegreeOneSmallSpectrum1060.graph fusedMap0554=true := by decide +kernel
theorem certified0554 : Certified (graph core0554) (root 10) 0 0 :=
  of_native_maps core0554 DegreeOneSmallSpectrum1061.graph DegreeOneSmallSpectrum1060.graph
    sourceMap0554 fusedMap0554 sourceMap0554_checked fusedMap0554_checked
    DegreeTwoThreeFiniteComparisons.comparison0554
#print axioms sourceMap0554_checked
#print axioms fusedMap0554_checked
#print axioms certified0554
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
