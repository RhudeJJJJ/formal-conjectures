/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0105 : Family 8 := level8.get ⟨139,by decide⟩
def sourceMap0105 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0105 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap0105_checked : acceptsGraphIso
    (source (graph core0105) (root 8) 0 0) DegreeOneSmallSpectrum327.graph sourceMap0105=true := by decide +kernel
theorem fusedMap0105_checked : acceptsGraphIso
    (fused (graph core0105) (root 8) 0 0) DegreeOneSmallSpectrum325.graph fusedMap0105=true := by decide +kernel
theorem certified0105 : Certified (graph core0105) (root 8) 0 0 :=
  of_native_maps core0105 DegreeOneSmallSpectrum327.graph DegreeOneSmallSpectrum325.graph
    sourceMap0105 fusedMap0105 sourceMap0105_checked fusedMap0105_checked
    DegreeTwoThreeFiniteComparisons.comparison0105
#print axioms sourceMap0105_checked
#print axioms fusedMap0105_checked
#print axioms certified0105
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
