/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0683 : Family 10 := level10.get ⟨284,by decide⟩
def sourceMap0683 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0683 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0683_checked : acceptsGraphIso
    (source (graph core0683) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1714.graph sourceMap0683=true := by decide +kernel
theorem fusedMap0683_checked : acceptsGraphIso
    (fused (graph core0683) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1235.graph fusedMap0683=true := by decide +kernel
theorem certified0683 : Certified (graph core0683) (root 10) 2 2 :=
  of_native_maps core0683 DegreeOneMiddleResidualSpectrum1714.graph DegreeOneMiddleResidualSpectrum1235.graph
    sourceMap0683 fusedMap0683 sourceMap0683_checked fusedMap0683_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0683
#print axioms sourceMap0683_checked
#print axioms fusedMap0683_checked
#print axioms certified0683
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
