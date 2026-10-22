/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0114 : Family 8 := level8.get ⟨162,by decide⟩
def sourceMap0114 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0114 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0114_checked : acceptsGraphIso
    (source (graph core0114) (root 8) 0 0) DegreeOneSmallSpectrum346.graph sourceMap0114=true := by decide +kernel
theorem fusedMap0114_checked : acceptsGraphIso
    (fused (graph core0114) (root 8) 0 0) DegreeOneSmallSpectrum341.graph fusedMap0114=true := by decide +kernel
theorem certified0114 : Certified (graph core0114) (root 8) 0 0 :=
  of_native_maps core0114 DegreeOneSmallSpectrum346.graph DegreeOneSmallSpectrum341.graph
    sourceMap0114 fusedMap0114 sourceMap0114_checked fusedMap0114_checked
    DegreeTwoThreeFiniteComparisons.comparison0114
#print axioms sourceMap0114_checked
#print axioms fusedMap0114_checked
#print axioms certified0114
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
