/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0662 : Family 10 := level10.get ⟨244,by decide⟩
def sourceMap0662 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0662 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0662_checked : acceptsGraphIso
    (source (graph core0662) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1671.graph sourceMap0662=true := by decide +kernel
theorem fusedMap0662_checked : acceptsGraphIso
    (fused (graph core0662) (root 10) 2 2) DegreeTwoThreeSpectrum5325.graph fusedMap0662=true := by decide +kernel
theorem certified0662 : Certified (graph core0662) (root 10) 2 2 :=
  of_native_maps core0662 DegreeOneMiddleResidualSpectrum1671.graph DegreeTwoThreeSpectrum5325.graph
    sourceMap0662 fusedMap0662 sourceMap0662_checked fusedMap0662_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0662
#print axioms sourceMap0662_checked
#print axioms fusedMap0662_checked
#print axioms certified0662
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
