/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0931 : Family 10 := level10.get ⟨739,by decide⟩
def sourceMap0931 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0931 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0931_checked : acceptsGraphIso
    (source (graph core0931) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2206.graph sourceMap0931=true := by decide +kernel
theorem fusedMap0931_checked : acceptsGraphIso
    (fused (graph core0931) (root 10) 2 2) DegreeTwoThreeSpectrum5500.graph fusedMap0931=true := by decide +kernel
theorem certified0931 : Certified (graph core0931) (root 10) 2 2 :=
  of_native_maps core0931 DegreeOneMiddleResidualSpectrum2206.graph DegreeTwoThreeSpectrum5500.graph
    sourceMap0931 fusedMap0931 sourceMap0931_checked fusedMap0931_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0931
#print axioms sourceMap0931_checked
#print axioms fusedMap0931_checked
#print axioms certified0931
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
