/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0382 : Family 9 := level9.get ⟨636,by decide⟩
def sourceMap0382 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0382 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0382_checked : acceptsGraphIso
    (source (graph core0382) (root 9) 0 0) SmallGeFourSpectrum171.graph sourceMap0382=true := by decide +kernel
theorem fusedMap0382_checked : acceptsGraphIso
    (fused (graph core0382) (root 9) 0 0) SmallGeFourSpectrum170.graph fusedMap0382=true := by decide +kernel
theorem certified0382 : Certified (graph core0382) (root 9) 0 0 :=
  of_native_maps core0382 SmallGeFourSpectrum171.graph SmallGeFourSpectrum170.graph
    sourceMap0382 fusedMap0382 sourceMap0382_checked fusedMap0382_checked
    DegreeTwoThreeFiniteComparisons.comparison0382
#print axioms sourceMap0382_checked
#print axioms fusedMap0382_checked
#print axioms certified0382
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
