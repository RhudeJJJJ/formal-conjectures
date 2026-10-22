/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0852 : Family 10 := level10.get ⟨579,by decide⟩
def sourceMap0852 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0852 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0852_checked : acceptsGraphIso
    (source (graph core0852) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2070.graph sourceMap0852=true := by decide +kernel
theorem fusedMap0852_checked : acceptsGraphIso
    (fused (graph core0852) (root 10) 2 2) DegreeTwoThreeSpectrum5248.graph fusedMap0852=true := by decide +kernel
theorem certified0852 : Certified (graph core0852) (root 10) 2 2 :=
  of_native_maps core0852 DegreeOneMiddleResidualSpectrum2070.graph DegreeTwoThreeSpectrum5248.graph
    sourceMap0852 fusedMap0852 sourceMap0852_checked fusedMap0852_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0852
#print axioms sourceMap0852_checked
#print axioms fusedMap0852_checked
#print axioms certified0852
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
