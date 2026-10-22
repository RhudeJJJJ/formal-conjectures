/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0562 : Family 10 := level10.get ⟨97,by decide⟩
def sourceMap0562 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0562 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0562_checked : acceptsGraphIso
    (source (graph core0562) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1781.graph sourceMap0562=true := by decide +kernel
theorem fusedMap0562_checked : acceptsGraphIso
    (fused (graph core0562) (root 10) 2 2) DegreeTwoThreeSpectrum5018.graph fusedMap0562=true := by decide +kernel
theorem certified0562 : Certified (graph core0562) (root 10) 2 2 :=
  of_native_maps core0562 DegreeOneMiddleResidualSpectrum1781.graph DegreeTwoThreeSpectrum5018.graph
    sourceMap0562 fusedMap0562 sourceMap0562_checked fusedMap0562_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0562
#print axioms sourceMap0562_checked
#print axioms fusedMap0562_checked
#print axioms certified0562
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
