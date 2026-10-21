/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1652 : Family 9 := level9.get ⟨394,by decide⟩
def sourceMap1652 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,8,6,7] (sourceLabel 9 0 1 v)
def fusedMap1652 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1652_checked : acceptsGraphIso
    (source (graph core1652) (root 9) 0 1) DegreeOneSmallSpectrum1874.graph sourceMap1652=true := by decide +kernel
theorem fusedMap1652_checked : acceptsGraphIso
    (fused (graph core1652) (root 9) 0 1) DegreeOneSmallSpectrum1197.graph fusedMap1652=true := by decide +kernel
theorem certified1652 : Certified (graph core1652) (root 9) 0 1 :=
  of_native_maps core1652 DegreeOneSmallSpectrum1874.graph DegreeOneSmallSpectrum1197.graph
    sourceMap1652 fusedMap1652 sourceMap1652_checked fusedMap1652_checked
    DegreeOneSmallComparisons.comparison1652
#print axioms sourceMap1652_checked
#print axioms fusedMap1652_checked
#print axioms certified1652
def sourceMap1652swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,6,7,8] (sourceLabel 9 1 0 v)
def fusedMap1652swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1652swap_checked : acceptsGraphIso
    (source (graph core1652) (root 9) 1 0) DegreeOneSmallSpectrum1874.graph sourceMap1652swap=true := by decide +kernel
theorem fusedMap1652swap_checked : acceptsGraphIso
    (fused (graph core1652) (root 9) 1 0) DegreeOneSmallSpectrum1197.graph fusedMap1652swap=true := by decide +kernel
theorem certified1652swap : Certified (graph core1652) (root 9) 1 0 :=
  of_native_maps core1652 DegreeOneSmallSpectrum1874.graph DegreeOneSmallSpectrum1197.graph
    sourceMap1652swap fusedMap1652swap sourceMap1652swap_checked fusedMap1652swap_checked
    DegreeOneSmallComparisons.comparison1652
#print axioms sourceMap1652swap_checked
#print axioms fusedMap1652swap_checked
#print axioms certified1652swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
