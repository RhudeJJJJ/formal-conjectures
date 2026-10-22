/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0555 : Family 10 := level10.get ⟨89,by decide⟩
def sourceMap0555 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0555 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0555_checked : acceptsGraphIso
    (source (graph core0555) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1744.graph sourceMap0555=true := by decide +kernel
theorem fusedMap0555_checked : acceptsGraphIso
    (fused (graph core0555) (root 10) 2 2) DegreeTwoThreeSpectrum5010.graph fusedMap0555=true := by decide +kernel
theorem certified0555 : Certified (graph core0555) (root 10) 2 2 :=
  of_native_maps core0555 DegreeOneMiddleResidualSpectrum1744.graph DegreeTwoThreeSpectrum5010.graph
    sourceMap0555 fusedMap0555 sourceMap0555_checked fusedMap0555_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0555
#print axioms sourceMap0555_checked
#print axioms fusedMap0555_checked
#print axioms certified0555
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
