/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0640 : Family 10 := level10.get ⟨215,by decide⟩
def sourceMap0640 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0640 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0640_checked : acceptsGraphIso
    (source (graph core0640) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1601.graph sourceMap0640=true := by decide +kernel
theorem fusedMap0640_checked : acceptsGraphIso
    (fused (graph core0640) (root 10) 2 2) DegreeTwoThreeSpectrum5228.graph fusedMap0640=true := by decide +kernel
theorem certified0640 : Certified (graph core0640) (root 10) 2 2 :=
  of_native_maps core0640 DegreeOneMiddleResidualSpectrum1601.graph DegreeTwoThreeSpectrum5228.graph
    sourceMap0640 fusedMap0640 sourceMap0640_checked fusedMap0640_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0640
#print axioms sourceMap0640_checked
#print axioms fusedMap0640_checked
#print axioms certified0640
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
