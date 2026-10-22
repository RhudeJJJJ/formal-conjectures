/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0501 : Family 10 := level10.get ⟨19,by decide⟩
def sourceMap0501 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0501 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0501_checked : acceptsGraphIso
    (source (graph core0501) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1303.graph sourceMap0501=true := by decide +kernel
theorem fusedMap0501_checked : acceptsGraphIso
    (fused (graph core0501) (root 10) 2 2) DegreeTwoThreeSpectrum5020.graph fusedMap0501=true := by decide +kernel
theorem certified0501 : Certified (graph core0501) (root 10) 2 2 :=
  of_native_maps core0501 DegreeOneMiddleResidualSpectrum1303.graph DegreeTwoThreeSpectrum5020.graph
    sourceMap0501 fusedMap0501 sourceMap0501_checked fusedMap0501_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0501
#print axioms sourceMap0501_checked
#print axioms fusedMap0501_checked
#print axioms certified0501
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
