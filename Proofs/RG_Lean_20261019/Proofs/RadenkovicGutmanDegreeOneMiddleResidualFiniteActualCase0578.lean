/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0578 : Family 10 := level10.get ⟨120,by decide⟩
def sourceMap0578 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0578 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0578_checked : acceptsGraphIso
    (source (graph core0578) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1899.graph sourceMap0578=true := by decide +kernel
theorem fusedMap0578_checked : acceptsGraphIso
    (fused (graph core0578) (root 10) 2 2) DegreeTwoThreeSpectrum5049.graph fusedMap0578=true := by decide +kernel
theorem certified0578 : Certified (graph core0578) (root 10) 2 2 :=
  of_native_maps core0578 DegreeOneMiddleResidualSpectrum1899.graph DegreeTwoThreeSpectrum5049.graph
    sourceMap0578 fusedMap0578 sourceMap0578_checked fusedMap0578_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0578
#print axioms sourceMap0578_checked
#print axioms fusedMap0578_checked
#print axioms certified0578
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
