/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0676 : Family 10 := level10.get ⟨265,by decide⟩
def sourceMap0676 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0676 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0676_checked : acceptsGraphIso
    (source (graph core0676) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1692.graph sourceMap0676=true := by decide +kernel
theorem fusedMap0676_checked : acceptsGraphIso
    (fused (graph core0676) (root 10) 2 2) DegreeTwoThreeSpectrum5382.graph fusedMap0676=true := by decide +kernel
theorem certified0676 : Certified (graph core0676) (root 10) 2 2 :=
  of_native_maps core0676 DegreeOneMiddleResidualSpectrum1692.graph DegreeTwoThreeSpectrum5382.graph
    sourceMap0676 fusedMap0676 sourceMap0676_checked fusedMap0676_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0676
#print axioms sourceMap0676_checked
#print axioms fusedMap0676_checked
#print axioms certified0676
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
