/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0967 : Family 10 := level10.get ⟨808,by decide⟩
def sourceMap0967 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0967 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0967_checked : acceptsGraphIso
    (source (graph core0967) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2255.graph sourceMap0967=true := by decide +kernel
theorem fusedMap0967_checked : acceptsGraphIso
    (fused (graph core0967) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1345.graph fusedMap0967=true := by decide +kernel
theorem certified0967 : Certified (graph core0967) (root 10) 2 2 :=
  of_native_maps core0967 DegreeOneMiddleResidualSpectrum2255.graph DegreeOneMiddleResidualSpectrum1345.graph
    sourceMap0967 fusedMap0967 sourceMap0967_checked fusedMap0967_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0967
#print axioms sourceMap0967_checked
#print axioms fusedMap0967_checked
#print axioms certified0967
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
