/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0493 : Family 10 := level10.get ⟨10,by decide⟩
def sourceMap0493 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0493 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0493_checked : acceptsGraphIso
    (source (graph core0493) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1120.graph sourceMap0493=true := by decide +kernel
theorem fusedMap0493_checked : acceptsGraphIso
    (fused (graph core0493) (root 10) 2 2) DegreeTwoThreeSpectrum4972.graph fusedMap0493=true := by decide +kernel
theorem certified0493 : Certified (graph core0493) (root 10) 2 2 :=
  of_native_maps core0493 DegreeOneMiddleResidualSpectrum1120.graph DegreeTwoThreeSpectrum4972.graph
    sourceMap0493 fusedMap0493 sourceMap0493_checked fusedMap0493_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0493
#print axioms sourceMap0493_checked
#print axioms fusedMap0493_checked
#print axioms certified0493
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
