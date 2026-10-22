/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0384 : Family 9 := level9.get ⟨296,by decide⟩
def sourceMap0384 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0384 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0384_checked : acceptsGraphIso
    (source (graph core0384) (root 9) 2 2) DegreeOneMiddleResidualSpectrum904.graph sourceMap0384=true := by decide +kernel
theorem fusedMap0384_checked : acceptsGraphIso
    (fused (graph core0384) (root 9) 2 2) DegreeOneMiddleResidualSpectrum540.graph fusedMap0384=true := by decide +kernel
theorem certified0384 : Certified (graph core0384) (root 9) 2 2 :=
  of_native_maps core0384 DegreeOneMiddleResidualSpectrum904.graph DegreeOneMiddleResidualSpectrum540.graph
    sourceMap0384 fusedMap0384 sourceMap0384_checked fusedMap0384_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0384
#print axioms sourceMap0384_checked
#print axioms fusedMap0384_checked
#print axioms certified0384
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
