/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0296 : Family 9 := level9.get ⟨140,by decide⟩
def sourceMap0296 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0296 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0296_checked : acceptsGraphIso
    (source (graph core0296) (root 9) 2 2) DegreeOneMiddleResidualSpectrum748.graph sourceMap0296=true := by decide +kernel
theorem fusedMap0296_checked : acceptsGraphIso
    (fused (graph core0296) (root 9) 2 2) DegreeTwoThreeSpectrum3895.graph fusedMap0296=true := by decide +kernel
theorem certified0296 : Certified (graph core0296) (root 9) 2 2 :=
  of_native_maps core0296 DegreeOneMiddleResidualSpectrum748.graph DegreeTwoThreeSpectrum3895.graph
    sourceMap0296 fusedMap0296 sourceMap0296_checked fusedMap0296_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0296
#print axioms sourceMap0296_checked
#print axioms fusedMap0296_checked
#print axioms certified0296
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
