/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0568 : Family 10 := level10.get ⟨105,by decide⟩
def sourceMap0568 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0568 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0568_checked : acceptsGraphIso
    (source (graph core0568) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1815.graph sourceMap0568=true := by decide +kernel
theorem fusedMap0568_checked : acceptsGraphIso
    (fused (graph core0568) (root 10) 2 2) DegreeTwoThreeSpectrum5028.graph fusedMap0568=true := by decide +kernel
theorem certified0568 : Certified (graph core0568) (root 10) 2 2 :=
  of_native_maps core0568 DegreeOneMiddleResidualSpectrum1815.graph DegreeTwoThreeSpectrum5028.graph
    sourceMap0568 fusedMap0568 sourceMap0568_checked fusedMap0568_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0568
#print axioms sourceMap0568_checked
#print axioms fusedMap0568_checked
#print axioms certified0568
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
