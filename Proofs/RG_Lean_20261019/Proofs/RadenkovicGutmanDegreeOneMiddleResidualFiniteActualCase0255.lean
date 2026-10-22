/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0255 : Family 9 := level9.get ⟨74,by decide⟩
def sourceMap0255 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0255 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0255_checked : acceptsGraphIso
    (source (graph core0255) (root 9) 2 2) DegreeOneMiddleResidualSpectrum659.graph sourceMap0255=true := by decide +kernel
theorem fusedMap0255_checked : acceptsGraphIso
    (fused (graph core0255) (root 9) 2 2) DegreeOneMiddleResidualSpectrum465.graph fusedMap0255=true := by decide +kernel
theorem certified0255 : Certified (graph core0255) (root 9) 2 2 :=
  of_native_maps core0255 DegreeOneMiddleResidualSpectrum659.graph DegreeOneMiddleResidualSpectrum465.graph
    sourceMap0255 fusedMap0255 sourceMap0255_checked fusedMap0255_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0255
#print axioms sourceMap0255_checked
#print axioms fusedMap0255_checked
#print axioms certified0255
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
