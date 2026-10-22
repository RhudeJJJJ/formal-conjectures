/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0339 : Family 9 := level9.get ⟨213,by decide⟩
def sourceMap0339 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0339 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0339_checked : acceptsGraphIso
    (source (graph core0339) (root 9) 2 2) DegreeOneMiddleResidualSpectrum837.graph sourceMap0339=true := by decide +kernel
theorem fusedMap0339_checked : acceptsGraphIso
    (fused (graph core0339) (root 9) 2 2) DegreeOneMiddleResidualSpectrum462.graph fusedMap0339=true := by decide +kernel
theorem certified0339 : Certified (graph core0339) (root 9) 2 2 :=
  of_native_maps core0339 DegreeOneMiddleResidualSpectrum837.graph DegreeOneMiddleResidualSpectrum462.graph
    sourceMap0339 fusedMap0339 sourceMap0339_checked fusedMap0339_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0339
#print axioms sourceMap0339_checked
#print axioms fusedMap0339_checked
#print axioms certified0339
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
