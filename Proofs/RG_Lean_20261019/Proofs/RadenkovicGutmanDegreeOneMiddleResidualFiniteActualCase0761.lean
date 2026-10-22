/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0761 : Family 10 := level10.get ⟨405,by decide⟩
def sourceMap0761 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0761 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0761_checked : acceptsGraphIso
    (source (graph core0761) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1917.graph sourceMap0761=true := by decide +kernel
theorem fusedMap0761_checked : acceptsGraphIso
    (fused (graph core0761) (root 10) 2 2) DegreeTwoThreeSpectrum5771.graph fusedMap0761=true := by decide +kernel
theorem certified0761 : Certified (graph core0761) (root 10) 2 2 :=
  of_native_maps core0761 DegreeOneMiddleResidualSpectrum1917.graph DegreeTwoThreeSpectrum5771.graph
    sourceMap0761 fusedMap0761 sourceMap0761_checked fusedMap0761_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0761
#print axioms sourceMap0761_checked
#print axioms fusedMap0761_checked
#print axioms certified0761
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
