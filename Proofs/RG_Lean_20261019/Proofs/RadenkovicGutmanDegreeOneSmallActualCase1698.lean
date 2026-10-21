/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1698 : Family 9 := level9.get ⟨462,by decide⟩
def sourceMap1698 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (sourceLabel 9 0 1 v)
def fusedMap1698 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1698_checked : acceptsGraphIso
    (source (graph core1698) (root 9) 0 1) DegreeOneSmallSpectrum1959.graph sourceMap1698=true := by decide +kernel
theorem fusedMap1698_checked : acceptsGraphIso
    (fused (graph core1698) (root 9) 0 1) DegreeOneSmallSpectrum1400.graph fusedMap1698=true := by decide +kernel
theorem certified1698 : Certified (graph core1698) (root 9) 0 1 :=
  of_native_maps core1698 DegreeOneSmallSpectrum1959.graph DegreeOneSmallSpectrum1400.graph
    sourceMap1698 fusedMap1698 sourceMap1698_checked fusedMap1698_checked
    DegreeOneSmallComparisons.comparison1698
#print axioms sourceMap1698_checked
#print axioms fusedMap1698_checked
#print axioms certified1698
def sourceMap1698swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 9 1 0 v)
def fusedMap1698swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1698swap_checked : acceptsGraphIso
    (source (graph core1698) (root 9) 1 0) DegreeOneSmallSpectrum1959.graph sourceMap1698swap=true := by decide +kernel
theorem fusedMap1698swap_checked : acceptsGraphIso
    (fused (graph core1698) (root 9) 1 0) DegreeOneSmallSpectrum1400.graph fusedMap1698swap=true := by decide +kernel
theorem certified1698swap : Certified (graph core1698) (root 9) 1 0 :=
  of_native_maps core1698 DegreeOneSmallSpectrum1959.graph DegreeOneSmallSpectrum1400.graph
    sourceMap1698swap fusedMap1698swap sourceMap1698swap_checked fusedMap1698swap_checked
    DegreeOneSmallComparisons.comparison1698
#print axioms sourceMap1698swap_checked
#print axioms fusedMap1698swap_checked
#print axioms certified1698swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
