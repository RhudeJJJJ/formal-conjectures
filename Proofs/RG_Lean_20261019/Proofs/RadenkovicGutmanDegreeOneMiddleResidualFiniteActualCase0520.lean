/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0520 : Family 10 := level10.get ⟨41,by decide⟩
def sourceMap0520 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0520 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0520_checked : acceptsGraphIso
    (source (graph core0520) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1378.graph sourceMap0520=true := by decide +kernel
theorem fusedMap0520_checked : acceptsGraphIso
    (fused (graph core0520) (root 10) 2 2) DegreeTwoThreeSpectrum5119.graph fusedMap0520=true := by decide +kernel
theorem certified0520 : Certified (graph core0520) (root 10) 2 2 :=
  of_native_maps core0520 DegreeOneMiddleResidualSpectrum1378.graph DegreeTwoThreeSpectrum5119.graph
    sourceMap0520 fusedMap0520 sourceMap0520_checked fusedMap0520_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0520
#print axioms sourceMap0520_checked
#print axioms fusedMap0520_checked
#print axioms certified0520
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
