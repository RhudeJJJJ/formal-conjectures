/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0756 : Family 10 := level10.get ⟨396,by decide⟩
def sourceMap0756 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0756 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0756_checked : acceptsGraphIso
    (source (graph core0756) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1880.graph sourceMap0756=true := by decide +kernel
theorem fusedMap0756_checked : acceptsGraphIso
    (fused (graph core0756) (root 10) 2 2) DegreeTwoThreeSpectrum5746.graph fusedMap0756=true := by decide +kernel
theorem certified0756 : Certified (graph core0756) (root 10) 2 2 :=
  of_native_maps core0756 DegreeOneMiddleResidualSpectrum1880.graph DegreeTwoThreeSpectrum5746.graph
    sourceMap0756 fusedMap0756 sourceMap0756_checked fusedMap0756_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0756
#print axioms sourceMap0756_checked
#print axioms fusedMap0756_checked
#print axioms certified0756
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
