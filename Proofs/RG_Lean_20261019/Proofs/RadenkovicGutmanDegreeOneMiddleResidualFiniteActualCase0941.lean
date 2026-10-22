/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0941 : Family 10 := level10.get ⟨755,by decide⟩
def sourceMap0941 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0941 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0941_checked : acceptsGraphIso
    (source (graph core0941) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2219.graph sourceMap0941=true := by decide +kernel
theorem fusedMap0941_checked : acceptsGraphIso
    (fused (graph core0941) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1298.graph fusedMap0941=true := by decide +kernel
theorem certified0941 : Certified (graph core0941) (root 10) 2 2 :=
  of_native_maps core0941 DegreeOneMiddleResidualSpectrum2219.graph DegreeOneMiddleResidualSpectrum1298.graph
    sourceMap0941 fusedMap0941 sourceMap0941_checked fusedMap0941_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0941
#print axioms sourceMap0941_checked
#print axioms fusedMap0941_checked
#print axioms certified0941
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
