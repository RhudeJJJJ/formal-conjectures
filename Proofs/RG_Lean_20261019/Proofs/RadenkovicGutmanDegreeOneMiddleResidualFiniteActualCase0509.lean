/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0509 : Family 10 := level10.get ⟨28,by decide⟩
def sourceMap0509 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0509 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0509_checked : acceptsGraphIso
    (source (graph core0509) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1382.graph sourceMap0509=true := by decide +kernel
theorem fusedMap0509_checked : acceptsGraphIso
    (fused (graph core0509) (root 10) 2 2) DegreeTwoThreeSpectrum5066.graph fusedMap0509=true := by decide +kernel
theorem certified0509 : Certified (graph core0509) (root 10) 2 2 :=
  of_native_maps core0509 DegreeOneMiddleResidualSpectrum1382.graph DegreeTwoThreeSpectrum5066.graph
    sourceMap0509 fusedMap0509 sourceMap0509_checked fusedMap0509_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0509
#print axioms sourceMap0509_checked
#print axioms fusedMap0509_checked
#print axioms certified0509
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
