/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0971 : Family 10 := level10.get ⟨831,by decide⟩
def sourceMap0971 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0971 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0971_checked : acceptsGraphIso
    (source (graph core0971) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2263.graph sourceMap0971=true := by decide +kernel
theorem fusedMap0971_checked : acceptsGraphIso
    (fused (graph core0971) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1364.graph fusedMap0971=true := by decide +kernel
theorem certified0971 : Certified (graph core0971) (root 10) 2 2 :=
  of_native_maps core0971 DegreeOneMiddleResidualSpectrum2263.graph DegreeOneMiddleResidualSpectrum1364.graph
    sourceMap0971 fusedMap0971 sourceMap0971_checked fusedMap0971_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0971
#print axioms sourceMap0971_checked
#print axioms fusedMap0971_checked
#print axioms certified0971
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
