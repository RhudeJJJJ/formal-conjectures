/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0727 : Family 10 := level10.get ⟨347,by decide⟩
def sourceMap0727 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0727 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0727_checked : acceptsGraphIso
    (source (graph core0727) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1816.graph sourceMap0727=true := by decide +kernel
theorem fusedMap0727_checked : acceptsGraphIso
    (fused (graph core0727) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1350.graph fusedMap0727=true := by decide +kernel
theorem certified0727 : Certified (graph core0727) (root 10) 2 2 :=
  of_native_maps core0727 DegreeOneMiddleResidualSpectrum1816.graph DegreeOneMiddleResidualSpectrum1350.graph
    sourceMap0727 fusedMap0727 sourceMap0727_checked fusedMap0727_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0727
#print axioms sourceMap0727_checked
#print axioms fusedMap0727_checked
#print axioms certified0727
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
