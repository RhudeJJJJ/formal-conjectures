/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0840 : Family 10 := level10.get ⟨561,by decide⟩
def sourceMap0840 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0840 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0840_checked : acceptsGraphIso
    (source (graph core0840) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2044.graph sourceMap0840=true := by decide +kernel
theorem fusedMap0840_checked : acceptsGraphIso
    (fused (graph core0840) (root 10) 2 2) DegreeTwoThreeSpectrum5226.graph fusedMap0840=true := by decide +kernel
theorem certified0840 : Certified (graph core0840) (root 10) 2 2 :=
  of_native_maps core0840 DegreeOneMiddleResidualSpectrum2044.graph DegreeTwoThreeSpectrum5226.graph
    sourceMap0840 fusedMap0840 sourceMap0840_checked fusedMap0840_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0840
#print axioms sourceMap0840_checked
#print axioms fusedMap0840_checked
#print axioms certified0840
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
