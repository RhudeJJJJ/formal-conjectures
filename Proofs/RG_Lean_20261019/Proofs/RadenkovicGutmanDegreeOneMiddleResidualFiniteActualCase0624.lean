/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0624 : Family 10 := level10.get ⟨192,by decide⟩
def sourceMap0624 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0624 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0624_checked : acceptsGraphIso
    (source (graph core0624) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1541.graph sourceMap0624=true := by decide +kernel
theorem fusedMap0624_checked : acceptsGraphIso
    (fused (graph core0624) (root 10) 2 2) DegreeTwoThreeSpectrum5153.graph fusedMap0624=true := by decide +kernel
theorem certified0624 : Certified (graph core0624) (root 10) 2 2 :=
  of_native_maps core0624 DegreeOneMiddleResidualSpectrum1541.graph DegreeTwoThreeSpectrum5153.graph
    sourceMap0624 fusedMap0624 sourceMap0624_checked fusedMap0624_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0624
#print axioms sourceMap0624_checked
#print axioms fusedMap0624_checked
#print axioms certified0624
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
