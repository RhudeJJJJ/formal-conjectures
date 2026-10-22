/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0851 : Family 10 := level10.get ⟨578,by decide⟩
def sourceMap0851 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0851 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0851_checked : acceptsGraphIso
    (source (graph core0851) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2069.graph sourceMap0851=true := by decide +kernel
theorem fusedMap0851_checked : acceptsGraphIso
    (fused (graph core0851) (root 10) 2 2) DegreeTwoThreeSpectrum5247.graph fusedMap0851=true := by decide +kernel
theorem certified0851 : Certified (graph core0851) (root 10) 2 2 :=
  of_native_maps core0851 DegreeOneMiddleResidualSpectrum2069.graph DegreeTwoThreeSpectrum5247.graph
    sourceMap0851 fusedMap0851 sourceMap0851_checked fusedMap0851_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0851
#print axioms sourceMap0851_checked
#print axioms fusedMap0851_checked
#print axioms certified0851
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
