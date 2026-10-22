/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0570 : Family 10 := level10.get ⟨107,by decide⟩
def sourceMap0570 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0570 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0570_checked : acceptsGraphIso
    (source (graph core0570) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1822.graph sourceMap0570=true := by decide +kernel
theorem fusedMap0570_checked : acceptsGraphIso
    (fused (graph core0570) (root 10) 2 2) DegreeTwoThreeSpectrum5030.graph fusedMap0570=true := by decide +kernel
theorem certified0570 : Certified (graph core0570) (root 10) 2 2 :=
  of_native_maps core0570 DegreeOneMiddleResidualSpectrum1822.graph DegreeTwoThreeSpectrum5030.graph
    sourceMap0570 fusedMap0570 sourceMap0570_checked fusedMap0570_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0570
#print axioms sourceMap0570_checked
#print axioms fusedMap0570_checked
#print axioms certified0570
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
