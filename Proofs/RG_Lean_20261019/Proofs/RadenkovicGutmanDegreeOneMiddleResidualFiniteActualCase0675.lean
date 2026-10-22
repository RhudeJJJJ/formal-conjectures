/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0675 : Family 10 := level10.get ⟨264,by decide⟩
def sourceMap0675 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0675 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0675_checked : acceptsGraphIso
    (source (graph core0675) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1691.graph sourceMap0675=true := by decide +kernel
theorem fusedMap0675_checked : acceptsGraphIso
    (fused (graph core0675) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1219.graph fusedMap0675=true := by decide +kernel
theorem certified0675 : Certified (graph core0675) (root 10) 2 2 :=
  of_native_maps core0675 DegreeOneMiddleResidualSpectrum1691.graph DegreeOneMiddleResidualSpectrum1219.graph
    sourceMap0675 fusedMap0675 sourceMap0675_checked fusedMap0675_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0675
#print axioms sourceMap0675_checked
#print axioms fusedMap0675_checked
#print axioms certified0675
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
