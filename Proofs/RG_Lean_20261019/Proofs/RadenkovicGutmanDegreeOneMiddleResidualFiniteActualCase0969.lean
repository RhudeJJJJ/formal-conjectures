/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0969 : Family 10 := level10.get ⟨813,by decide⟩
def sourceMap0969 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0969 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0969_checked : acceptsGraphIso
    (source (graph core0969) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2257.graph sourceMap0969=true := by decide +kernel
theorem fusedMap0969_checked : acceptsGraphIso
    (fused (graph core0969) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1349.graph fusedMap0969=true := by decide +kernel
theorem certified0969 : Certified (graph core0969) (root 10) 2 2 :=
  of_native_maps core0969 DegreeOneMiddleResidualSpectrum2257.graph DegreeOneMiddleResidualSpectrum1349.graph
    sourceMap0969 fusedMap0969 sourceMap0969_checked fusedMap0969_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0969
#print axioms sourceMap0969_checked
#print axioms fusedMap0969_checked
#print axioms certified0969
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
