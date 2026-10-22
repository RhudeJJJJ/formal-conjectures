/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0867 : Family 10 := level10.get ⟨604,by decide⟩
def sourceMap0867 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0867 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0867_checked : acceptsGraphIso
    (source (graph core0867) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2097.graph sourceMap0867=true := by decide +kernel
theorem fusedMap0867_checked : acceptsGraphIso
    (fused (graph core0867) (root 10) 2 2) DegreeTwoThreeSpectrum5283.graph fusedMap0867=true := by decide +kernel
theorem certified0867 : Certified (graph core0867) (root 10) 2 2 :=
  of_native_maps core0867 DegreeOneMiddleResidualSpectrum2097.graph DegreeTwoThreeSpectrum5283.graph
    sourceMap0867 fusedMap0867 sourceMap0867_checked fusedMap0867_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0867
#print axioms sourceMap0867_checked
#print axioms fusedMap0867_checked
#print axioms certified0867
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
