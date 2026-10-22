/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0530 : Family 10 := level10.get ⟨56,by decide⟩
def sourceMap0530 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0530 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0530_checked : acceptsGraphIso
    (source (graph core0530) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1588.graph sourceMap0530=true := by decide +kernel
theorem fusedMap0530_checked : acceptsGraphIso
    (fused (graph core0530) (root 10) 2 2) DegreeTwoThreeSpectrum4968.graph fusedMap0530=true := by decide +kernel
theorem certified0530 : Certified (graph core0530) (root 10) 2 2 :=
  of_native_maps core0530 DegreeOneMiddleResidualSpectrum1588.graph DegreeTwoThreeSpectrum4968.graph
    sourceMap0530 fusedMap0530 sourceMap0530_checked fusedMap0530_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0530
#print axioms sourceMap0530_checked
#print axioms fusedMap0530_checked
#print axioms certified0530
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
