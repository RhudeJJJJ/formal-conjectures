/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0912 : Family 10 := level10.get ⟨702,by decide⟩
def sourceMap0912 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0912 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0912_checked : acceptsGraphIso
    (source (graph core0912) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2174.graph sourceMap0912=true := by decide +kernel
theorem fusedMap0912_checked : acceptsGraphIso
    (fused (graph core0912) (root 10) 2 2) DegreeTwoThreeSpectrum5443.graph fusedMap0912=true := by decide +kernel
theorem certified0912 : Certified (graph core0912) (root 10) 2 2 :=
  of_native_maps core0912 DegreeOneMiddleResidualSpectrum2174.graph DegreeTwoThreeSpectrum5443.graph
    sourceMap0912 fusedMap0912 sourceMap0912_checked fusedMap0912_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0912
#print axioms sourceMap0912_checked
#print axioms fusedMap0912_checked
#print axioms certified0912
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
