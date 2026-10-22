/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0601 : Family 10 := level10.get ⟨151,by decide⟩
def sourceMap0601 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0601 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0601_checked : acceptsGraphIso
    (source (graph core0601) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1937.graph sourceMap0601=true := by decide +kernel
theorem fusedMap0601_checked : acceptsGraphIso
    (fused (graph core0601) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1031.graph fusedMap0601=true := by decide +kernel
theorem certified0601 : Certified (graph core0601) (root 10) 2 2 :=
  of_native_maps core0601 DegreeOneMiddleResidualSpectrum1937.graph DegreeOneMiddleResidualSpectrum1031.graph
    sourceMap0601 fusedMap0601 sourceMap0601_checked fusedMap0601_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0601
#print axioms sourceMap0601_checked
#print axioms fusedMap0601_checked
#print axioms certified0601
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
