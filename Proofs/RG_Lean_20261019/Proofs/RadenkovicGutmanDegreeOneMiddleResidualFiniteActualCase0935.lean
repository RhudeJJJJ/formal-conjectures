/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0935 : Family 10 := level10.get ⟨744,by decide⟩
def sourceMap0935 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0935 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0935_checked : acceptsGraphIso
    (source (graph core0935) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2213.graph sourceMap0935=true := by decide +kernel
theorem fusedMap0935_checked : acceptsGraphIso
    (fused (graph core0935) (root 10) 2 2) DegreeTwoThreeSpectrum5505.graph fusedMap0935=true := by decide +kernel
theorem certified0935 : Certified (graph core0935) (root 10) 2 2 :=
  of_native_maps core0935 DegreeOneMiddleResidualSpectrum2213.graph DegreeTwoThreeSpectrum5505.graph
    sourceMap0935 fusedMap0935 sourceMap0935_checked fusedMap0935_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0935
#print axioms sourceMap0935_checked
#print axioms fusedMap0935_checked
#print axioms certified0935
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
