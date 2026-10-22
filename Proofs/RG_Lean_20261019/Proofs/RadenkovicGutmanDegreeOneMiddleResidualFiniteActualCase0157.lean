/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0157 : Family 8 := level8.get ⟨167,by decide⟩
def sourceMap0157 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,7,8,9,10,11,12,13,14,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap0157 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0157_checked : acceptsGraphIso
    (source (graph core0157) (root 8) 2 2) DegreeOneMiddleResidualSpectrum330.graph sourceMap0157=true := by decide +kernel
theorem fusedMap0157_checked : acceptsGraphIso
    (fused (graph core0157) (root 8) 2 2) DegreeOneMiddleResidualSpectrum251.graph fusedMap0157=true := by decide +kernel
theorem certified0157 : Certified (graph core0157) (root 8) 2 2 :=
  of_native_maps core0157 DegreeOneMiddleResidualSpectrum330.graph DegreeOneMiddleResidualSpectrum251.graph
    sourceMap0157 fusedMap0157 sourceMap0157_checked fusedMap0157_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0157
#print axioms sourceMap0157_checked
#print axioms fusedMap0157_checked
#print axioms certified0157
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
