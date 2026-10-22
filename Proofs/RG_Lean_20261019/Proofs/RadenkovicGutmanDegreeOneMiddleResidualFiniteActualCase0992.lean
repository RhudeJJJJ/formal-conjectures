/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0992 : Family 10 := level10.get ⟨867,by decide⟩
def sourceMap0992 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0992 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0992_checked : acceptsGraphIso
    (source (graph core0992) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2294.graph sourceMap0992=true := by decide +kernel
theorem fusedMap0992_checked : acceptsGraphIso
    (fused (graph core0992) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1419.graph fusedMap0992=true := by decide +kernel
theorem certified0992 : Certified (graph core0992) (root 10) 2 2 :=
  of_native_maps core0992 DegreeOneMiddleResidualSpectrum2294.graph DegreeOneMiddleResidualSpectrum1419.graph
    sourceMap0992 fusedMap0992 sourceMap0992_checked fusedMap0992_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0992
#print axioms sourceMap0992_checked
#print axioms fusedMap0992_checked
#print axioms certified0992
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
