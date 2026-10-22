/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0382 : Family 9 := level9.get ⟨293,by decide⟩
def sourceMap0382 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0382 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0382_checked : acceptsGraphIso
    (source (graph core0382) (root 9) 2 2) DegreeOneMiddleResidualSpectrum902.graph sourceMap0382=true := by decide +kernel
theorem fusedMap0382_checked : acceptsGraphIso
    (fused (graph core0382) (root 9) 2 2) DegreeTwoThreeSpectrum4122.graph fusedMap0382=true := by decide +kernel
theorem certified0382 : Certified (graph core0382) (root 9) 2 2 :=
  of_native_maps core0382 DegreeOneMiddleResidualSpectrum902.graph DegreeTwoThreeSpectrum4122.graph
    sourceMap0382 fusedMap0382 sourceMap0382_checked fusedMap0382_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0382
#print axioms sourceMap0382_checked
#print axioms fusedMap0382_checked
#print axioms certified0382
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
