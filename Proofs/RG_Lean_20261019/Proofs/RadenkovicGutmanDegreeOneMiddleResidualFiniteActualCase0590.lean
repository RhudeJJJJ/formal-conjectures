/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0590 : Family 10 := level10.get ⟨134,by decide⟩
def sourceMap0590 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0590 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0590_checked : acceptsGraphIso
    (source (graph core0590) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1884.graph sourceMap0590=true := by decide +kernel
theorem fusedMap0590_checked : acceptsGraphIso
    (fused (graph core0590) (root 10) 2 2) DegreeTwoThreeSpectrum5064.graph fusedMap0590=true := by decide +kernel
theorem certified0590 : Certified (graph core0590) (root 10) 2 2 :=
  of_native_maps core0590 DegreeOneMiddleResidualSpectrum1884.graph DegreeTwoThreeSpectrum5064.graph
    sourceMap0590 fusedMap0590 sourceMap0590_checked fusedMap0590_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0590
#print axioms sourceMap0590_checked
#print axioms fusedMap0590_checked
#print axioms certified0590
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
