/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0121 : Family 8 := level8.get ⟨95,by decide⟩
def sourceMap0121 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0121 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0121_checked : acceptsGraphIso
    (source (graph core0121) (root 8) 2 2) DegreeOneMiddleResidualSpectrum262.graph sourceMap0121=true := by decide +kernel
theorem fusedMap0121_checked : acceptsGraphIso
    (fused (graph core0121) (root 8) 2 2) DegreeOneMiddleResidualSpectrum170.graph fusedMap0121=true := by decide +kernel
theorem certified0121 : Certified (graph core0121) (root 8) 2 2 :=
  of_native_maps core0121 DegreeOneMiddleResidualSpectrum262.graph DegreeOneMiddleResidualSpectrum170.graph
    sourceMap0121 fusedMap0121 sourceMap0121_checked fusedMap0121_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0121
#print axioms sourceMap0121_checked
#print axioms fusedMap0121_checked
#print axioms certified0121
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
