/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0828 : Family 10 := level10.get ⟨1281,by decide⟩
def sourceMap0828 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0828 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,9,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap0828_checked : acceptsGraphIso
    (source (graph core0828) (root 10) 0 0) DegreeOneSmallSpectrum1644.graph sourceMap0828=true := by decide +kernel
theorem fusedMap0828_checked : acceptsGraphIso
    (fused (graph core0828) (root 10) 0 0) DegreeOneSmallSpectrum1925.graph fusedMap0828=true := by decide +kernel
theorem certified0828 : Certified (graph core0828) (root 10) 0 0 :=
  of_native_maps core0828 DegreeOneSmallSpectrum1644.graph DegreeOneSmallSpectrum1925.graph
    sourceMap0828 fusedMap0828 sourceMap0828_checked fusedMap0828_checked
    DegreeTwoThreeFiniteComparisons.comparison0828
#print axioms sourceMap0828_checked
#print axioms fusedMap0828_checked
#print axioms certified0828
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
