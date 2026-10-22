/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0930 : Family 10 := level10.get ⟨738,by decide⟩
def sourceMap0930 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0930 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0930_checked : acceptsGraphIso
    (source (graph core0930) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2203.graph sourceMap0930=true := by decide +kernel
theorem fusedMap0930_checked : acceptsGraphIso
    (fused (graph core0930) (root 10) 2 2) DegreeTwoThreeSpectrum5499.graph fusedMap0930=true := by decide +kernel
theorem certified0930 : Certified (graph core0930) (root 10) 2 2 :=
  of_native_maps core0930 DegreeOneMiddleResidualSpectrum2203.graph DegreeTwoThreeSpectrum5499.graph
    sourceMap0930 fusedMap0930 sourceMap0930_checked fusedMap0930_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0930
#print axioms sourceMap0930_checked
#print axioms fusedMap0930_checked
#print axioms certified0930
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
