/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0627 : Family 10 := level10.get ⟨196,by decide⟩
def sourceMap0627 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0627 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0627_checked : acceptsGraphIso
    (source (graph core0627) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1563.graph sourceMap0627=true := by decide +kernel
theorem fusedMap0627_checked : acceptsGraphIso
    (fused (graph core0627) (root 10) 2 2) DegreeTwoThreeSpectrum5168.graph fusedMap0627=true := by decide +kernel
theorem certified0627 : Certified (graph core0627) (root 10) 2 2 :=
  of_native_maps core0627 DegreeOneMiddleResidualSpectrum1563.graph DegreeTwoThreeSpectrum5168.graph
    sourceMap0627 fusedMap0627 sourceMap0627_checked fusedMap0627_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0627
#print axioms sourceMap0627_checked
#print axioms fusedMap0627_checked
#print axioms certified0627
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
