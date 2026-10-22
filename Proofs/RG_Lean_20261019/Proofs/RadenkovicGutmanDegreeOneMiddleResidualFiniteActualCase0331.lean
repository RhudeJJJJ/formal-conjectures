/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0331 : Family 9 := level9.get ⟨200,by decide⟩
def sourceMap0331 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0331 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0331_checked : acceptsGraphIso
    (source (graph core0331) (root 9) 2 2) DegreeOneMiddleResidualSpectrum821.graph sourceMap0331=true := by decide +kernel
theorem fusedMap0331_checked : acceptsGraphIso
    (fused (graph core0331) (root 9) 2 2) DegreeOneMiddleResidualSpectrum450.graph fusedMap0331=true := by decide +kernel
theorem certified0331 : Certified (graph core0331) (root 9) 2 2 :=
  of_native_maps core0331 DegreeOneMiddleResidualSpectrum821.graph DegreeOneMiddleResidualSpectrum450.graph
    sourceMap0331 fusedMap0331 sourceMap0331_checked fusedMap0331_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0331
#print axioms sourceMap0331_checked
#print axioms fusedMap0331_checked
#print axioms certified0331
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
