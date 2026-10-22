/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0358 : Family 9 := level9.get ⟨243,by decide⟩
def sourceMap0358 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap0358 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0358_checked : acceptsGraphIso
    (source (graph core0358) (root 9) 2 2) DegreeOneMiddleResidualSpectrum869.graph sourceMap0358=true := by decide +kernel
theorem fusedMap0358_checked : acceptsGraphIso
    (fused (graph core0358) (root 9) 2 2) DegreeOneMiddleResidualSpectrum490.graph fusedMap0358=true := by decide +kernel
theorem certified0358 : Certified (graph core0358) (root 9) 2 2 :=
  of_native_maps core0358 DegreeOneMiddleResidualSpectrum869.graph DegreeOneMiddleResidualSpectrum490.graph
    sourceMap0358 fusedMap0358 sourceMap0358_checked fusedMap0358_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0358
#print axioms sourceMap0358_checked
#print axioms fusedMap0358_checked
#print axioms certified0358
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
