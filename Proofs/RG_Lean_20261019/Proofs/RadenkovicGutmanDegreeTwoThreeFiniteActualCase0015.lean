/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0015 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap0015 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,6,7,8,2,3,4,5] (sourceLabel 6 0 0 v)
def fusedMap0015 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,0,6,7,8,2,3,4,5] (fusedLabel 6 0 0 v)
theorem sourceMap0015_checked : acceptsGraphIso
    (source (graph core0015) (root 6) 0 0) DegreeOneSmallSpectrum058.graph sourceMap0015=true := by decide +kernel
theorem fusedMap0015_checked : acceptsGraphIso
    (fused (graph core0015) (root 6) 0 0) DegreeOneSmallSpectrum055.graph fusedMap0015=true := by decide +kernel
theorem certified0015 : Certified (graph core0015) (root 6) 0 0 :=
  of_native_maps core0015 DegreeOneSmallSpectrum058.graph DegreeOneSmallSpectrum055.graph
    sourceMap0015 fusedMap0015 sourceMap0015_checked fusedMap0015_checked
    DegreeTwoThreeFiniteComparisons.comparison0015
#print axioms sourceMap0015_checked
#print axioms fusedMap0015_checked
#print axioms certified0015
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
