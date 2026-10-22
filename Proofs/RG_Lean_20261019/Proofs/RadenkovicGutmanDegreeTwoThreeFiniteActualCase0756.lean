/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0756 : Family 10 := level10.get ⟨1105,by decide⟩
def sourceMap0756 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0756 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0756_checked : acceptsGraphIso
    (source (graph core0756) (root 10) 0 0) DegreeOneSmallSpectrum1672.graph sourceMap0756=true := by decide +kernel
theorem fusedMap0756_checked : acceptsGraphIso
    (fused (graph core0756) (root 10) 0 0) DegreeOneSmallSpectrum1732.graph fusedMap0756=true := by decide +kernel
theorem certified0756 : Certified (graph core0756) (root 10) 0 0 :=
  of_native_maps core0756 DegreeOneSmallSpectrum1672.graph DegreeOneSmallSpectrum1732.graph
    sourceMap0756 fusedMap0756 sourceMap0756_checked fusedMap0756_checked
    DegreeTwoThreeFiniteComparisons.comparison0756
#print axioms sourceMap0756_checked
#print axioms fusedMap0756_checked
#print axioms certified0756
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
