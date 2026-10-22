/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0715 : Family 10 := level10.get ⟨329,by decide⟩
def sourceMap0715 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0715 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0715_checked : acceptsGraphIso
    (source (graph core0715) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1799.graph sourceMap0715=true := by decide +kernel
theorem fusedMap0715_checked : acceptsGraphIso
    (fused (graph core0715) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1322.graph fusedMap0715=true := by decide +kernel
theorem certified0715 : Certified (graph core0715) (root 10) 2 2 :=
  of_native_maps core0715 DegreeOneMiddleResidualSpectrum1799.graph DegreeOneMiddleResidualSpectrum1322.graph
    sourceMap0715 fusedMap0715 sourceMap0715_checked fusedMap0715_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0715
#print axioms sourceMap0715_checked
#print axioms fusedMap0715_checked
#print axioms certified0715
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
