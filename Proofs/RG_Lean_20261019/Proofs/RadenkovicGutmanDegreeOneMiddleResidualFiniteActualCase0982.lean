/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0982 : Family 10 := level10.get ⟨848,by decide⟩
def sourceMap0982 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0982 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0982_checked : acceptsGraphIso
    (source (graph core0982) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2281.graph sourceMap0982=true := by decide +kernel
theorem fusedMap0982_checked : acceptsGraphIso
    (fused (graph core0982) (root 10) 2 2) DegreeTwoThreeSpectrum5681.graph fusedMap0982=true := by decide +kernel
theorem certified0982 : Certified (graph core0982) (root 10) 2 2 :=
  of_native_maps core0982 DegreeOneMiddleResidualSpectrum2281.graph DegreeTwoThreeSpectrum5681.graph
    sourceMap0982 fusedMap0982 sourceMap0982_checked fusedMap0982_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0982
#print axioms sourceMap0982_checked
#print axioms fusedMap0982_checked
#print axioms certified0982
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
