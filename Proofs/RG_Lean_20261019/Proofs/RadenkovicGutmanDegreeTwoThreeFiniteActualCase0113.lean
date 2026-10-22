/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0113 : Family 8 := level8.get ⟨158,by decide⟩
def sourceMap0113 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (sourceLabel 8 0 0 v)
def fusedMap0113 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,2,3,4,5,6] (fusedLabel 8 0 0 v)
theorem sourceMap0113_checked : acceptsGraphIso
    (source (graph core0113) (root 8) 0 0) DegreeOneSmallSpectrum290.graph sourceMap0113=true := by decide +kernel
theorem fusedMap0113_checked : acceptsGraphIso
    (fused (graph core0113) (root 8) 0 0) DegreeOneSmallSpectrum280.graph fusedMap0113=true := by decide +kernel
theorem certified0113 : Certified (graph core0113) (root 8) 0 0 :=
  of_native_maps core0113 DegreeOneSmallSpectrum290.graph DegreeOneSmallSpectrum280.graph
    sourceMap0113 fusedMap0113 sourceMap0113_checked fusedMap0113_checked
    DegreeTwoThreeFiniteComparisons.comparison0113
#print axioms sourceMap0113_checked
#print axioms fusedMap0113_checked
#print axioms certified0113
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
