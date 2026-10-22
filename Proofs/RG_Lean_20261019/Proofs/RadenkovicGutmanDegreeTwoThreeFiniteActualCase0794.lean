/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0794 : Family 10 := level10.get ⟨1198,by decide⟩
def sourceMap0794 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,10,11,12,6,7,8,9] (sourceLabel 10 0 0 v)
def fusedMap0794 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,10,11,12,6,7,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0794_checked : acceptsGraphIso
    (source (graph core0794) (root 10) 0 0) DegreeOneSmallSpectrum1867.graph sourceMap0794=true := by decide +kernel
theorem fusedMap0794_checked : acceptsGraphIso
    (fused (graph core0794) (root 10) 0 0) DegreeOneSmallSpectrum1858.graph fusedMap0794=true := by decide +kernel
theorem certified0794 : Certified (graph core0794) (root 10) 0 0 :=
  of_native_maps core0794 DegreeOneSmallSpectrum1867.graph DegreeOneSmallSpectrum1858.graph
    sourceMap0794 fusedMap0794 sourceMap0794_checked fusedMap0794_checked
    DegreeTwoThreeFiniteComparisons.comparison0794
#print axioms sourceMap0794_checked
#print axioms fusedMap0794_checked
#print axioms certified0794
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
