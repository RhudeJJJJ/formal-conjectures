/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0382 : Family 6 := level6.get ⟨15,by decide⟩
def sourceMap0382 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (sourceLabel 6 1 3 v)
def fusedMap0382 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0382_checked : acceptsGraphIso
    (source (graph core0382) (root 6) 1 3) DegreeOneSmallSpectrum1500.graph sourceMap0382=true := by decide +kernel
theorem fusedMap0382_checked : acceptsGraphIso
    (fused (graph core0382) (root 6) 1 3) DegreeOneSmallSpectrum956.graph fusedMap0382=true := by decide +kernel
theorem certified0382 : Certified (graph core0382) (root 6) 1 3 :=
  of_native_maps core0382 DegreeOneSmallSpectrum1500.graph DegreeOneSmallSpectrum956.graph
    sourceMap0382 fusedMap0382 sourceMap0382_checked fusedMap0382_checked
    DegreeOneSmallComparisons.comparison0382
#print axioms sourceMap0382_checked
#print axioms fusedMap0382_checked
#print axioms certified0382
def sourceMap0382swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 3 1 v)
def fusedMap0382swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0382swap_checked : acceptsGraphIso
    (source (graph core0382) (root 6) 3 1) DegreeOneSmallSpectrum1500.graph sourceMap0382swap=true := by decide +kernel
theorem fusedMap0382swap_checked : acceptsGraphIso
    (fused (graph core0382) (root 6) 3 1) DegreeOneSmallSpectrum956.graph fusedMap0382swap=true := by decide +kernel
theorem certified0382swap : Certified (graph core0382) (root 6) 3 1 :=
  of_native_maps core0382 DegreeOneSmallSpectrum1500.graph DegreeOneSmallSpectrum956.graph
    sourceMap0382swap fusedMap0382swap sourceMap0382swap_checked fusedMap0382swap_checked
    DegreeOneSmallComparisons.comparison0382
#print axioms sourceMap0382swap_checked
#print axioms fusedMap0382swap_checked
#print axioms certified0382swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
