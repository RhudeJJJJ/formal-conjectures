/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0537 : Family 10 := level10.get ⟨64,by decide⟩
def sourceMap0537 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0537 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0537_checked : acceptsGraphIso
    (source (graph core0537) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1654.graph sourceMap0537=true := by decide +kernel
theorem fusedMap0537_checked : acceptsGraphIso
    (fused (graph core0537) (root 10) 2 2) DegreeTwoThreeSpectrum4977.graph fusedMap0537=true := by decide +kernel
theorem certified0537 : Certified (graph core0537) (root 10) 2 2 :=
  of_native_maps core0537 DegreeOneMiddleResidualSpectrum1654.graph DegreeTwoThreeSpectrum4977.graph
    sourceMap0537 fusedMap0537 sourceMap0537_checked fusedMap0537_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0537
#print axioms sourceMap0537_checked
#print axioms fusedMap0537_checked
#print axioms certified0537
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
