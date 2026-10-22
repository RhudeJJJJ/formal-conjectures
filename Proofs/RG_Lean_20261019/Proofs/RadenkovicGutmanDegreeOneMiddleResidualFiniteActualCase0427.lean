/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0427 : Family 9 := level9.get ⟨398,by decide⟩
def sourceMap0427 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0427 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0427_checked : acceptsGraphIso
    (source (graph core0427) (root 9) 2 2) DegreeOneMiddleResidualSpectrum807.graph sourceMap0427=true := by decide +kernel
theorem fusedMap0427_checked : acceptsGraphIso
    (fused (graph core0427) (root 9) 2 2) DegreeOneMiddleResidualSpectrum623.graph fusedMap0427=true := by decide +kernel
theorem certified0427 : Certified (graph core0427) (root 9) 2 2 :=
  of_native_maps core0427 DegreeOneMiddleResidualSpectrum807.graph DegreeOneMiddleResidualSpectrum623.graph
    sourceMap0427 fusedMap0427 sourceMap0427_checked fusedMap0427_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0427
#print axioms sourceMap0427_checked
#print axioms fusedMap0427_checked
#print axioms certified0427
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
