/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0310 : Family 9 := level9.get ⟨161,by decide⟩
def sourceMap0310 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0310 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0310_checked : acceptsGraphIso
    (source (graph core0310) (root 9) 2 2) DegreeOneMiddleResidualSpectrum782.graph sourceMap0310=true := by decide +kernel
theorem fusedMap0310_checked : acceptsGraphIso
    (fused (graph core0310) (root 9) 2 2) DegreeOneMiddleResidualSpectrum415.graph fusedMap0310=true := by decide +kernel
theorem certified0310 : Certified (graph core0310) (root 9) 2 2 :=
  of_native_maps core0310 DegreeOneMiddleResidualSpectrum782.graph DegreeOneMiddleResidualSpectrum415.graph
    sourceMap0310 fusedMap0310 sourceMap0310_checked fusedMap0310_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0310
#print axioms sourceMap0310_checked
#print axioms fusedMap0310_checked
#print axioms certified0310
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
