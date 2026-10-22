/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0679 : Family 10 := level10.get ⟨272,by decide⟩
def sourceMap0679 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0679 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0679_checked : acceptsGraphIso
    (source (graph core0679) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1698.graph sourceMap0679=true := by decide +kernel
theorem fusedMap0679_checked : acceptsGraphIso
    (fused (graph core0679) (root 10) 2 2) DegreeTwoThreeSpectrum5400.graph fusedMap0679=true := by decide +kernel
theorem certified0679 : Certified (graph core0679) (root 10) 2 2 :=
  of_native_maps core0679 DegreeOneMiddleResidualSpectrum1698.graph DegreeTwoThreeSpectrum5400.graph
    sourceMap0679 fusedMap0679 sourceMap0679_checked fusedMap0679_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0679
#print axioms sourceMap0679_checked
#print axioms fusedMap0679_checked
#print axioms certified0679
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
