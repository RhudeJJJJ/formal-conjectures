/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0745 : Family 10 := level10.get ⟨379,by decide⟩
def sourceMap0745 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0745 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0745_checked : acceptsGraphIso
    (source (graph core0745) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1876.graph sourceMap0745=true := by decide +kernel
theorem fusedMap0745_checked : acceptsGraphIso
    (fused (graph core0745) (root 10) 2 2) DegreeTwoThreeSpectrum5700.graph fusedMap0745=true := by decide +kernel
theorem certified0745 : Certified (graph core0745) (root 10) 2 2 :=
  of_native_maps core0745 DegreeOneMiddleResidualSpectrum1876.graph DegreeTwoThreeSpectrum5700.graph
    sourceMap0745 fusedMap0745 sourceMap0745_checked fusedMap0745_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0745
#print axioms sourceMap0745_checked
#print axioms fusedMap0745_checked
#print axioms certified0745
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
