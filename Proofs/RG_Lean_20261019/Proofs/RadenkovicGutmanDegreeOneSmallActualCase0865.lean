/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0865 : Family 8 := level8.get ⟨41,by decide⟩
def sourceMap0865 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0865 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0865_checked : acceptsGraphIso
    (source (graph core0865) (root 8) 0 2) DegreeOneSmallSpectrum1157.graph sourceMap0865=true := by decide +kernel
theorem fusedMap0865_checked : acceptsGraphIso
    (fused (graph core0865) (root 8) 0 2) DegreeOneSmallSpectrum873.graph fusedMap0865=true := by decide +kernel
theorem certified0865 : Certified (graph core0865) (root 8) 0 2 :=
  of_native_maps core0865 DegreeOneSmallSpectrum1157.graph DegreeOneSmallSpectrum873.graph
    sourceMap0865 fusedMap0865 sourceMap0865_checked fusedMap0865_checked
    DegreeOneSmallComparisons.comparison0865
#print axioms sourceMap0865_checked
#print axioms fusedMap0865_checked
#print axioms certified0865
def sourceMap0865swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0865swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0865swap_checked : acceptsGraphIso
    (source (graph core0865) (root 8) 2 0) DegreeOneSmallSpectrum1157.graph sourceMap0865swap=true := by decide +kernel
theorem fusedMap0865swap_checked : acceptsGraphIso
    (fused (graph core0865) (root 8) 2 0) DegreeOneSmallSpectrum873.graph fusedMap0865swap=true := by decide +kernel
theorem certified0865swap : Certified (graph core0865) (root 8) 2 0 :=
  of_native_maps core0865 DegreeOneSmallSpectrum1157.graph DegreeOneSmallSpectrum873.graph
    sourceMap0865swap fusedMap0865swap sourceMap0865swap_checked fusedMap0865swap_checked
    DegreeOneSmallComparisons.comparison0865
#print axioms sourceMap0865swap_checked
#print axioms fusedMap0865swap_checked
#print axioms certified0865swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
