/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0545 : Family 10 := level10.get ⟨74,by decide⟩
def sourceMap0545 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0545 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0545_checked : acceptsGraphIso
    (source (graph core0545) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1693.graph sourceMap0545=true := by decide +kernel
theorem fusedMap0545_checked : acceptsGraphIso
    (fused (graph core0545) (root 10) 2 2) DegreeTwoThreeSpectrum4989.graph fusedMap0545=true := by decide +kernel
theorem certified0545 : Certified (graph core0545) (root 10) 2 2 :=
  of_native_maps core0545 DegreeOneMiddleResidualSpectrum1693.graph DegreeTwoThreeSpectrum4989.graph
    sourceMap0545 fusedMap0545 sourceMap0545_checked fusedMap0545_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0545
#print axioms sourceMap0545_checked
#print axioms fusedMap0545_checked
#print axioms certified0545
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
