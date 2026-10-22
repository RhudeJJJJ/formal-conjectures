/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0587 : Family 10 := level10.get ⟨131,by decide⟩
def sourceMap0587 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0587 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0587_checked : acceptsGraphIso
    (source (graph core0587) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1918.graph sourceMap0587=true := by decide +kernel
theorem fusedMap0587_checked : acceptsGraphIso
    (fused (graph core0587) (root 10) 2 2) DegreeTwoThreeSpectrum5061.graph fusedMap0587=true := by decide +kernel
theorem certified0587 : Certified (graph core0587) (root 10) 2 2 :=
  of_native_maps core0587 DegreeOneMiddleResidualSpectrum1918.graph DegreeTwoThreeSpectrum5061.graph
    sourceMap0587 fusedMap0587 sourceMap0587_checked fusedMap0587_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0587
#print axioms sourceMap0587_checked
#print axioms fusedMap0587_checked
#print axioms certified0587
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
