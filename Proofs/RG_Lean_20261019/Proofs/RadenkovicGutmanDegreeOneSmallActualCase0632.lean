/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0632 : Family 7 := level7.get ⟨43,by decide⟩
def sourceMap0632 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0632 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0632_checked : acceptsGraphIso
    (source (graph core0632) (root 7) 1 2) DegreeOneSmallSpectrum1377.graph sourceMap0632=true := by decide +kernel
theorem fusedMap0632_checked : acceptsGraphIso
    (fused (graph core0632) (root 7) 1 2) DegreeOneSmallSpectrum917.graph fusedMap0632=true := by decide +kernel
theorem certified0632 : Certified (graph core0632) (root 7) 1 2 :=
  of_native_maps core0632 DegreeOneSmallSpectrum1377.graph DegreeOneSmallSpectrum917.graph
    sourceMap0632 fusedMap0632 sourceMap0632_checked fusedMap0632_checked
    DegreeOneSmallComparisons.comparison0632
#print axioms sourceMap0632_checked
#print axioms fusedMap0632_checked
#print axioms certified0632
def sourceMap0632swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0632swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0632swap_checked : acceptsGraphIso
    (source (graph core0632) (root 7) 2 1) DegreeOneSmallSpectrum1377.graph sourceMap0632swap=true := by decide +kernel
theorem fusedMap0632swap_checked : acceptsGraphIso
    (fused (graph core0632) (root 7) 2 1) DegreeOneSmallSpectrum917.graph fusedMap0632swap=true := by decide +kernel
theorem certified0632swap : Certified (graph core0632) (root 7) 2 1 :=
  of_native_maps core0632 DegreeOneSmallSpectrum1377.graph DegreeOneSmallSpectrum917.graph
    sourceMap0632swap fusedMap0632swap sourceMap0632swap_checked fusedMap0632swap_checked
    DegreeOneSmallComparisons.comparison0632
#print axioms sourceMap0632swap_checked
#print axioms fusedMap0632swap_checked
#print axioms certified0632swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
