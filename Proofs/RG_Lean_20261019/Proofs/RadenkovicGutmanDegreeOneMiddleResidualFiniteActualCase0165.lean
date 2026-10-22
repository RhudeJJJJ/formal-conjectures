/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0165 : Family 8 := level8.get ⟨199,by decide⟩
def sourceMap0165 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0165 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0165_checked : acceptsGraphIso
    (source (graph core0165) (root 8) 2 2) DegreeOneMiddleResidualSpectrum349.graph sourceMap0165=true := by decide +kernel
theorem fusedMap0165_checked : acceptsGraphIso
    (fused (graph core0165) (root 8) 2 2) DegreeOneMiddleResidualSpectrum178.graph fusedMap0165=true := by decide +kernel
theorem certified0165 : Certified (graph core0165) (root 8) 2 2 :=
  of_native_maps core0165 DegreeOneMiddleResidualSpectrum349.graph DegreeOneMiddleResidualSpectrum178.graph
    sourceMap0165 fusedMap0165 sourceMap0165_checked fusedMap0165_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0165
#print axioms sourceMap0165_checked
#print axioms fusedMap0165_checked
#print axioms certified0165
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
