/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0577 : Family 10 := level10.get ⟨119,by decide⟩
def sourceMap0577 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0577 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0577_checked : acceptsGraphIso
    (source (graph core0577) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1895.graph sourceMap0577=true := by decide +kernel
theorem fusedMap0577_checked : acceptsGraphIso
    (fused (graph core0577) (root 10) 2 2) DegreeTwoThreeSpectrum5048.graph fusedMap0577=true := by decide +kernel
theorem certified0577 : Certified (graph core0577) (root 10) 2 2 :=
  of_native_maps core0577 DegreeOneMiddleResidualSpectrum1895.graph DegreeTwoThreeSpectrum5048.graph
    sourceMap0577 fusedMap0577 sourceMap0577_checked fusedMap0577_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0577
#print axioms sourceMap0577_checked
#print axioms fusedMap0577_checked
#print axioms certified0577
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
