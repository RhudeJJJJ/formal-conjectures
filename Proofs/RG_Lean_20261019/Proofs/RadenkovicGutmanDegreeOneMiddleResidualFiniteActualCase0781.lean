/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0781 : Family 10 := level10.get ⟨440,by decide⟩
def sourceMap0781 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0781 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0781_checked : acceptsGraphIso
    (source (graph core0781) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1888.graph sourceMap0781=true := by decide +kernel
theorem fusedMap0781_checked : acceptsGraphIso
    (fused (graph core0781) (root 10) 2 2) DegreeTwoThreeSpectrum5854.graph fusedMap0781=true := by decide +kernel
theorem certified0781 : Certified (graph core0781) (root 10) 2 2 :=
  of_native_maps core0781 DegreeOneMiddleResidualSpectrum1888.graph DegreeTwoThreeSpectrum5854.graph
    sourceMap0781 fusedMap0781 sourceMap0781_checked fusedMap0781_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0781
#print axioms sourceMap0781_checked
#print axioms fusedMap0781_checked
#print axioms certified0781
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
