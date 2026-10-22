/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0823 : Family 10 := level10.get ⟨527,by decide⟩
def sourceMap0823 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0823 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0823_checked : acceptsGraphIso
    (source (graph core0823) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2014.graph sourceMap0823=true := by decide +kernel
theorem fusedMap0823_checked : acceptsGraphIso
    (fused (graph core0823) (root 10) 2 2) DegreeTwoThreeSpectrum5171.graph fusedMap0823=true := by decide +kernel
theorem certified0823 : Certified (graph core0823) (root 10) 2 2 :=
  of_native_maps core0823 DegreeOneMiddleResidualSpectrum2014.graph DegreeTwoThreeSpectrum5171.graph
    sourceMap0823 fusedMap0823 sourceMap0823_checked fusedMap0823_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0823
#print axioms sourceMap0823_checked
#print axioms fusedMap0823_checked
#print axioms certified0823
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
