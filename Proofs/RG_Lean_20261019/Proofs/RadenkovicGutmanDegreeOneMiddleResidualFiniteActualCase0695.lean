/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0695 : Family 10 := level10.get ⟨299,by decide⟩
def sourceMap0695 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0695 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0695_checked : acceptsGraphIso
    (source (graph core0695) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1745.graph sourceMap0695=true := by decide +kernel
theorem fusedMap0695_checked : acceptsGraphIso
    (fused (graph core0695) (root 10) 2 2) DegreeTwoThreeSpectrum5474.graph fusedMap0695=true := by decide +kernel
theorem certified0695 : Certified (graph core0695) (root 10) 2 2 :=
  of_native_maps core0695 DegreeOneMiddleResidualSpectrum1745.graph DegreeTwoThreeSpectrum5474.graph
    sourceMap0695 fusedMap0695 sourceMap0695_checked fusedMap0695_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0695
#print axioms sourceMap0695_checked
#print axioms fusedMap0695_checked
#print axioms certified0695
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
