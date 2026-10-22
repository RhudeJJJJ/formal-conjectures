/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0831 : Family 10 := level10.get ⟨540,by decide⟩
def sourceMap0831 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0831 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0831_checked : acceptsGraphIso
    (source (graph core0831) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2030.graph sourceMap0831=true := by decide +kernel
theorem fusedMap0831_checked : acceptsGraphIso
    (fused (graph core0831) (root 10) 2 2) DegreeTwoThreeSpectrum5189.graph fusedMap0831=true := by decide +kernel
theorem certified0831 : Certified (graph core0831) (root 10) 2 2 :=
  of_native_maps core0831 DegreeOneMiddleResidualSpectrum2030.graph DegreeTwoThreeSpectrum5189.graph
    sourceMap0831 fusedMap0831 sourceMap0831_checked fusedMap0831_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0831
#print axioms sourceMap0831_checked
#print axioms fusedMap0831_checked
#print axioms certified0831
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
