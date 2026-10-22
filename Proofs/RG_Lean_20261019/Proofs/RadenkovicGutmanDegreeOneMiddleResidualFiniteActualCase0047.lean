/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0047 : Family 7 := level7.get ⟨100,by decide⟩
def sourceMap0047 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,1,2,3,4,5,6] (sourceLabel 7 2 2 v)
def fusedMap0047 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0047_checked : acceptsGraphIso
    (source (graph core0047) (root 7) 2 2) DegreeOneMiddleResidualSpectrum104.graph sourceMap0047=true := by decide +kernel
theorem fusedMap0047_checked : acceptsGraphIso
    (fused (graph core0047) (root 7) 2 2) DegreeOneMiddleResidualSpectrum057.graph fusedMap0047=true := by decide +kernel
theorem certified0047 : Certified (graph core0047) (root 7) 2 2 :=
  of_native_maps core0047 DegreeOneMiddleResidualSpectrum104.graph DegreeOneMiddleResidualSpectrum057.graph
    sourceMap0047 fusedMap0047 sourceMap0047_checked fusedMap0047_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0047
#print axioms sourceMap0047_checked
#print axioms fusedMap0047_checked
#print axioms certified0047
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
