/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0385 : Family 9 := level9.get ⟨300,by decide⟩
def sourceMap0385 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0385 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0385_checked : acceptsGraphIso
    (source (graph core0385) (root 9) 2 2) DegreeOneMiddleResidualSpectrum905.graph sourceMap0385=true := by decide +kernel
theorem fusedMap0385_checked : acceptsGraphIso
    (fused (graph core0385) (root 9) 2 2) DegreeOneMiddleResidualSpectrum543.graph fusedMap0385=true := by decide +kernel
theorem certified0385 : Certified (graph core0385) (root 9) 2 2 :=
  of_native_maps core0385 DegreeOneMiddleResidualSpectrum905.graph DegreeOneMiddleResidualSpectrum543.graph
    sourceMap0385 fusedMap0385 sourceMap0385_checked fusedMap0385_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0385
#print axioms sourceMap0385_checked
#print axioms fusedMap0385_checked
#print axioms certified0385
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
