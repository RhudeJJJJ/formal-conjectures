/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0639 : Family 10 := level10.get ⟨211,by decide⟩
def sourceMap0639 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0639 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0639_checked : acceptsGraphIso
    (source (graph core0639) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1590.graph sourceMap0639=true := by decide +kernel
theorem fusedMap0639_checked : acceptsGraphIso
    (fused (graph core0639) (root 10) 2 2) DegreeTwoThreeSpectrum5217.graph fusedMap0639=true := by decide +kernel
theorem certified0639 : Certified (graph core0639) (root 10) 2 2 :=
  of_native_maps core0639 DegreeOneMiddleResidualSpectrum1590.graph DegreeTwoThreeSpectrum5217.graph
    sourceMap0639 fusedMap0639 sourceMap0639_checked fusedMap0639_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0639
#print axioms sourceMap0639_checked
#print axioms fusedMap0639_checked
#print axioms certified0639
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
