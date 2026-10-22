/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0633 : Family 10 := level10.get ⟨203,by decide⟩
def sourceMap0633 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0633 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0633_checked : acceptsGraphIso
    (source (graph core0633) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1582.graph sourceMap0633=true := by decide +kernel
theorem fusedMap0633_checked : acceptsGraphIso
    (fused (graph core0633) (root 10) 2 2) DegreeTwoThreeSpectrum5195.graph fusedMap0633=true := by decide +kernel
theorem certified0633 : Certified (graph core0633) (root 10) 2 2 :=
  of_native_maps core0633 DegreeOneMiddleResidualSpectrum1582.graph DegreeTwoThreeSpectrum5195.graph
    sourceMap0633 fusedMap0633 sourceMap0633_checked fusedMap0633_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0633
#print axioms sourceMap0633_checked
#print axioms fusedMap0633_checked
#print axioms certified0633
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
