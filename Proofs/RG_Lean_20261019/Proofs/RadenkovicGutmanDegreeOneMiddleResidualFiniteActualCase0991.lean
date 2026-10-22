/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0991 : Family 10 := level10.get ⟨865,by decide⟩
def sourceMap0991 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0991 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0991_checked : acceptsGraphIso
    (source (graph core0991) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2293.graph sourceMap0991=true := by decide +kernel
theorem fusedMap0991_checked : acceptsGraphIso
    (fused (graph core0991) (root 10) 2 2) DegreeTwoThreeSpectrum5705.graph fusedMap0991=true := by decide +kernel
theorem certified0991 : Certified (graph core0991) (root 10) 2 2 :=
  of_native_maps core0991 DegreeOneMiddleResidualSpectrum2293.graph DegreeTwoThreeSpectrum5705.graph
    sourceMap0991 fusedMap0991 sourceMap0991_checked fusedMap0991_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0991
#print axioms sourceMap0991_checked
#print axioms fusedMap0991_checked
#print axioms certified0991
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
