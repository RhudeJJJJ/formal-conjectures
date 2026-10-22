/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0780 : Family 10 := level10.get ⟨439,by decide⟩
def sourceMap0780 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0780 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0780_checked : acceptsGraphIso
    (source (graph core0780) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1933.graph sourceMap0780=true := by decide +kernel
theorem fusedMap0780_checked : acceptsGraphIso
    (fused (graph core0780) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1485.graph fusedMap0780=true := by decide +kernel
theorem certified0780 : Certified (graph core0780) (root 10) 2 2 :=
  of_native_maps core0780 DegreeOneMiddleResidualSpectrum1933.graph DegreeOneMiddleResidualSpectrum1485.graph
    sourceMap0780 fusedMap0780 sourceMap0780_checked fusedMap0780_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0780
#print axioms sourceMap0780_checked
#print axioms fusedMap0780_checked
#print axioms certified0780
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
