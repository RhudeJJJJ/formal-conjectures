/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0698 : Family 10 := level10.get ⟨305,by decide⟩
def sourceMap0698 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0698 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0698_checked : acceptsGraphIso
    (source (graph core0698) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1759.graph sourceMap0698=true := by decide +kernel
theorem fusedMap0698_checked : acceptsGraphIso
    (fused (graph core0698) (root 10) 2 2) DegreeTwoThreeSpectrum5489.graph fusedMap0698=true := by decide +kernel
theorem certified0698 : Certified (graph core0698) (root 10) 2 2 :=
  of_native_maps core0698 DegreeOneMiddleResidualSpectrum1759.graph DegreeTwoThreeSpectrum5489.graph
    sourceMap0698 fusedMap0698 sourceMap0698_checked fusedMap0698_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0698
#print axioms sourceMap0698_checked
#print axioms fusedMap0698_checked
#print axioms certified0698
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
