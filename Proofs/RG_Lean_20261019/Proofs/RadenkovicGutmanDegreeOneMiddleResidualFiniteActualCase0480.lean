/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0480 : Family 9 := level9.get ⟨630,by decide⟩
def sourceMap0480 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0480 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0480_checked : acceptsGraphIso
    (source (graph core0480) (root 9) 2 2) DegreeOneMiddleResidualSpectrum924.graph sourceMap0480=true := by decide +kernel
theorem fusedMap0480_checked : acceptsGraphIso
    (fused (graph core0480) (root 9) 2 2) DegreeOneMiddleResidualSpectrum637.graph fusedMap0480=true := by decide +kernel
theorem certified0480 : Certified (graph core0480) (root 9) 2 2 :=
  of_native_maps core0480 DegreeOneMiddleResidualSpectrum924.graph DegreeOneMiddleResidualSpectrum637.graph
    sourceMap0480 fusedMap0480 sourceMap0480_checked fusedMap0480_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0480
#print axioms sourceMap0480_checked
#print axioms fusedMap0480_checked
#print axioms certified0480
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
