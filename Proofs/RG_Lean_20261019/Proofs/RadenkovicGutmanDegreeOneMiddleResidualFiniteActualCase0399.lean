/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0399 : Family 9 := level9.get ⟨337,by decide⟩
def sourceMap0399 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0399 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0399_checked : acceptsGraphIso
    (source (graph core0399) (root 9) 2 2) DegreeOneMiddleResidualSpectrum756.graph sourceMap0399=true := by decide +kernel
theorem fusedMap0399_checked : acceptsGraphIso
    (fused (graph core0399) (root 9) 2 2) DegreeTwoThreeSpectrum4225.graph fusedMap0399=true := by decide +kernel
theorem certified0399 : Certified (graph core0399) (root 9) 2 2 :=
  of_native_maps core0399 DegreeOneMiddleResidualSpectrum756.graph DegreeTwoThreeSpectrum4225.graph
    sourceMap0399 fusedMap0399 sourceMap0399_checked fusedMap0399_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0399
#print axioms sourceMap0399_checked
#print axioms fusedMap0399_checked
#print axioms certified0399
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
