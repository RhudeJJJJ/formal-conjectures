/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0932 : Family 10 := level10.get ⟨740,by decide⟩
def sourceMap0932 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0932 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0932_checked : acceptsGraphIso
    (source (graph core0932) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2209.graph sourceMap0932=true := by decide +kernel
theorem fusedMap0932_checked : acceptsGraphIso
    (fused (graph core0932) (root 10) 2 2) DegreeTwoThreeSpectrum5501.graph fusedMap0932=true := by decide +kernel
theorem certified0932 : Certified (graph core0932) (root 10) 2 2 :=
  of_native_maps core0932 DegreeOneMiddleResidualSpectrum2209.graph DegreeTwoThreeSpectrum5501.graph
    sourceMap0932 fusedMap0932 sourceMap0932_checked fusedMap0932_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0932
#print axioms sourceMap0932_checked
#print axioms fusedMap0932_checked
#print axioms certified0932
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
