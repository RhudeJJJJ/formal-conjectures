/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0645 : Family 10 := level10.get ⟨221,by decide⟩
def sourceMap0645 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0645 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0645_checked : acceptsGraphIso
    (source (graph core0645) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1625.graph sourceMap0645=true := by decide +kernel
theorem fusedMap0645_checked : acceptsGraphIso
    (fused (graph core0645) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1141.graph fusedMap0645=true := by decide +kernel
theorem certified0645 : Certified (graph core0645) (root 10) 2 2 :=
  of_native_maps core0645 DegreeOneMiddleResidualSpectrum1625.graph DegreeOneMiddleResidualSpectrum1141.graph
    sourceMap0645 fusedMap0645 sourceMap0645_checked fusedMap0645_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0645
#print axioms sourceMap0645_checked
#print axioms fusedMap0645_checked
#print axioms certified0645
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
