/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0801 : Family 10 := level10.get ⟨497,by decide⟩
def sourceMap0801 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0801 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0801_checked : acceptsGraphIso
    (source (graph core0801) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1960.graph sourceMap0801=true := by decide +kernel
theorem fusedMap0801_checked : acceptsGraphIso
    (fused (graph core0801) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1064.graph fusedMap0801=true := by decide +kernel
theorem certified0801 : Certified (graph core0801) (root 10) 2 2 :=
  of_native_maps core0801 DegreeOneMiddleResidualSpectrum1960.graph DegreeOneMiddleResidualSpectrum1064.graph
    sourceMap0801 fusedMap0801 sourceMap0801_checked fusedMap0801_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0801
#print axioms sourceMap0801_checked
#print axioms fusedMap0801_checked
#print axioms certified0801
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
