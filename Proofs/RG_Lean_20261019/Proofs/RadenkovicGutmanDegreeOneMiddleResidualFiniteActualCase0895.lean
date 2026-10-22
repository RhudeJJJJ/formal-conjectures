/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0895 : Family 10 := level10.get ⟨659,by decide⟩
def sourceMap0895 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0895 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0895_checked : acceptsGraphIso
    (source (graph core0895) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2138.graph sourceMap0895=true := by decide +kernel
theorem fusedMap0895_checked : acceptsGraphIso
    (fused (graph core0895) (root 10) 2 2) DegreeTwoThreeSpectrum5369.graph fusedMap0895=true := by decide +kernel
theorem certified0895 : Certified (graph core0895) (root 10) 2 2 :=
  of_native_maps core0895 DegreeOneMiddleResidualSpectrum2138.graph DegreeTwoThreeSpectrum5369.graph
    sourceMap0895 fusedMap0895 sourceMap0895_checked fusedMap0895_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0895
#print axioms sourceMap0895_checked
#print axioms fusedMap0895_checked
#print axioms certified0895
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
