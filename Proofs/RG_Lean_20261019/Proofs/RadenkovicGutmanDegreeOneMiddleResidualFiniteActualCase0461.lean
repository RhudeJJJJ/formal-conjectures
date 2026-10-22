/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0461 : Family 9 := level9.get ⟨509,by decide⟩
def sourceMap0461 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,7,8,9,10,11,12,13,14,15,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap0461 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0461_checked : acceptsGraphIso
    (source (graph core0461) (root 9) 2 2) DegreeOneMiddleResidualSpectrum888.graph sourceMap0461=true := by decide +kernel
theorem fusedMap0461_checked : acceptsGraphIso
    (fused (graph core0461) (root 9) 2 2) DegreeOneMiddleResidualSpectrum735.graph fusedMap0461=true := by decide +kernel
theorem certified0461 : Certified (graph core0461) (root 9) 2 2 :=
  of_native_maps core0461 DegreeOneMiddleResidualSpectrum888.graph DegreeOneMiddleResidualSpectrum735.graph
    sourceMap0461 fusedMap0461 sourceMap0461_checked fusedMap0461_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0461
#print axioms sourceMap0461_checked
#print axioms fusedMap0461_checked
#print axioms certified0461
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
