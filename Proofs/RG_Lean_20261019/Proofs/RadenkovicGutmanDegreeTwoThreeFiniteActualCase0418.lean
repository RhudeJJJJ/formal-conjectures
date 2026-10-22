/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0418 : Family 10 := level10.get ⟨109,by decide⟩
def sourceMap0418 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0418 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0418_checked : acceptsGraphIso
    (source (graph core0418) (root 10) 0 0) DegreeOneSmallSpectrum1073.graph sourceMap0418=true := by decide +kernel
theorem fusedMap0418_checked : acceptsGraphIso
    (fused (graph core0418) (root 10) 0 0) DegreeOneSmallSpectrum932.graph fusedMap0418=true := by decide +kernel
theorem certified0418 : Certified (graph core0418) (root 10) 0 0 :=
  of_native_maps core0418 DegreeOneSmallSpectrum1073.graph DegreeOneSmallSpectrum932.graph
    sourceMap0418 fusedMap0418 sourceMap0418_checked fusedMap0418_checked
    DegreeTwoThreeFiniteComparisons.comparison0418
#print axioms sourceMap0418_checked
#print axioms fusedMap0418_checked
#print axioms certified0418
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
