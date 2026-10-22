/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0750 : Family 10 := level10.get ⟨386,by decide⟩
def sourceMap0750 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0750 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0750_checked : acceptsGraphIso
    (source (graph core0750) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1866.graph sourceMap0750=true := by decide +kernel
theorem fusedMap0750_checked : acceptsGraphIso
    (fused (graph core0750) (root 10) 2 2) DegreeTwoThreeSpectrum5719.graph fusedMap0750=true := by decide +kernel
theorem certified0750 : Certified (graph core0750) (root 10) 2 2 :=
  of_native_maps core0750 DegreeOneMiddleResidualSpectrum1866.graph DegreeTwoThreeSpectrum5719.graph
    sourceMap0750 fusedMap0750 sourceMap0750_checked fusedMap0750_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0750
#print axioms sourceMap0750_checked
#print axioms fusedMap0750_checked
#print axioms certified0750
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
