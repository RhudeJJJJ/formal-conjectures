/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0511 : Family 10 := level10.get ⟨30,by decide⟩
def sourceMap0511 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0511 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0511_checked : acceptsGraphIso
    (source (graph core0511) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1376.graph sourceMap0511=true := by decide +kernel
theorem fusedMap0511_checked : acceptsGraphIso
    (fused (graph core0511) (root 10) 2 2) DegreeTwoThreeSpectrum5075.graph fusedMap0511=true := by decide +kernel
theorem certified0511 : Certified (graph core0511) (root 10) 2 2 :=
  of_native_maps core0511 DegreeOneMiddleResidualSpectrum1376.graph DegreeTwoThreeSpectrum5075.graph
    sourceMap0511 fusedMap0511 sourceMap0511_checked fusedMap0511_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0511
#print axioms sourceMap0511_checked
#print axioms fusedMap0511_checked
#print axioms certified0511
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
