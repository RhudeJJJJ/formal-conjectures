/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0019 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap0019 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,2,3,4] (sourceLabel 6 0 0 v)
def fusedMap0019 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,8,6,7] (fusedLabel 6 0 0 v)
theorem sourceMap0019_checked : acceptsGraphIso
    (source (graph core0019) (root 6) 0 0) DegreeOneSmallSpectrum068.graph sourceMap0019=true := by decide +kernel
theorem fusedMap0019_checked : acceptsGraphIso
    (fused (graph core0019) (root 6) 0 0) DegreeOneSmallSpectrum054.graph fusedMap0019=true := by decide +kernel
theorem certified0019 : Certified (graph core0019) (root 6) 0 0 :=
  of_native_maps core0019 DegreeOneSmallSpectrum068.graph DegreeOneSmallSpectrum054.graph
    sourceMap0019 fusedMap0019 sourceMap0019_checked fusedMap0019_checked
    DegreeTwoThreeFiniteComparisons.comparison0019
#print axioms sourceMap0019_checked
#print axioms fusedMap0019_checked
#print axioms certified0019
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
