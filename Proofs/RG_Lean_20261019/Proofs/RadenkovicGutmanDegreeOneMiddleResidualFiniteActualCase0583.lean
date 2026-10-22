/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0583 : Family 10 := level10.get ⟨126,by decide⟩
def sourceMap0583 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0583 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0583_checked : acceptsGraphIso
    (source (graph core0583) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1910.graph sourceMap0583=true := by decide +kernel
theorem fusedMap0583_checked : acceptsGraphIso
    (fused (graph core0583) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1007.graph fusedMap0583=true := by decide +kernel
theorem certified0583 : Certified (graph core0583) (root 10) 2 2 :=
  of_native_maps core0583 DegreeOneMiddleResidualSpectrum1910.graph DegreeOneMiddleResidualSpectrum1007.graph
    sourceMap0583 fusedMap0583 sourceMap0583_checked fusedMap0583_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0583
#print axioms sourceMap0583_checked
#print axioms fusedMap0583_checked
#print axioms certified0583
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
