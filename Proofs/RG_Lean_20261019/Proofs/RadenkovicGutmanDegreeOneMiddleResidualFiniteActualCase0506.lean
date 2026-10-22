/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0506 : Family 10 := level10.get ⟨24,by decide⟩
def sourceMap0506 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0506 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap0506_checked : acceptsGraphIso
    (source (graph core0506) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1360.graph sourceMap0506=true := by decide +kernel
theorem fusedMap0506_checked : acceptsGraphIso
    (fused (graph core0506) (root 10) 2 2) DegreeTwoThreeSpectrum5047.graph fusedMap0506=true := by decide +kernel
theorem certified0506 : Certified (graph core0506) (root 10) 2 2 :=
  of_native_maps core0506 DegreeOneMiddleResidualSpectrum1360.graph DegreeTwoThreeSpectrum5047.graph
    sourceMap0506 fusedMap0506 sourceMap0506_checked fusedMap0506_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0506
#print axioms sourceMap0506_checked
#print axioms fusedMap0506_checked
#print axioms certified0506
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
