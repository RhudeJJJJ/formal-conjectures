/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0169 : Family 8 := level8.get ⟨214,by decide⟩
def sourceMap0169 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0169 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0169_checked : acceptsGraphIso
    (source (graph core0169) (root 8) 2 2) DegreeOneMiddleResidualSpectrum353.graph sourceMap0169=true := by decide +kernel
theorem fusedMap0169_checked : acceptsGraphIso
    (fused (graph core0169) (root 8) 2 2) DegreeOneMiddleResidualSpectrum191.graph fusedMap0169=true := by decide +kernel
theorem certified0169 : Certified (graph core0169) (root 8) 2 2 :=
  of_native_maps core0169 DegreeOneMiddleResidualSpectrum353.graph DegreeOneMiddleResidualSpectrum191.graph
    sourceMap0169 fusedMap0169 sourceMap0169_checked fusedMap0169_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0169
#print axioms sourceMap0169_checked
#print axioms fusedMap0169_checked
#print axioms certified0169
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
