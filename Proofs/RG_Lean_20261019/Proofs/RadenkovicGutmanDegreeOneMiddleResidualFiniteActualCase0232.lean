/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0232 : Family 9 := level9.get ⟨43,by decide⟩
def sourceMap0232 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0232 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0232_checked : acceptsGraphIso
    (source (graph core0232) (root 9) 2 2) DegreeOneMiddleResidualSpectrum567.graph sourceMap0232=true := by decide +kernel
theorem fusedMap0232_checked : acceptsGraphIso
    (fused (graph core0232) (root 9) 2 2) DegreeOneMiddleResidualSpectrum396.graph fusedMap0232=true := by decide +kernel
theorem certified0232 : Certified (graph core0232) (root 9) 2 2 :=
  of_native_maps core0232 DegreeOneMiddleResidualSpectrum567.graph DegreeOneMiddleResidualSpectrum396.graph
    sourceMap0232 fusedMap0232 sourceMap0232_checked fusedMap0232_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0232
#print axioms sourceMap0232_checked
#print axioms fusedMap0232_checked
#print axioms certified0232
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
