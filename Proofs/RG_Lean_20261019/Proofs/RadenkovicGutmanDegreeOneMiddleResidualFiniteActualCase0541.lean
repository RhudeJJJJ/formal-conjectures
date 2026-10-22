/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0541 : Family 10 := level10.get ⟨69,by decide⟩
def sourceMap0541 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0541 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0541_checked : acceptsGraphIso
    (source (graph core0541) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1681.graph sourceMap0541=true := by decide +kernel
theorem fusedMap0541_checked : acceptsGraphIso
    (fused (graph core0541) (root 10) 2 2) DegreeTwoThreeSpectrum4983.graph fusedMap0541=true := by decide +kernel
theorem certified0541 : Certified (graph core0541) (root 10) 2 2 :=
  of_native_maps core0541 DegreeOneMiddleResidualSpectrum1681.graph DegreeTwoThreeSpectrum4983.graph
    sourceMap0541 fusedMap0541 sourceMap0541_checked fusedMap0541_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0541
#print axioms sourceMap0541_checked
#print axioms fusedMap0541_checked
#print axioms certified0541
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
