/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1021 : Family 8 := level8.get ⟨109,by decide⟩
def sourceMap1021 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1021 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1021_checked : acceptsGraphIso
    (source (graph core1021) (root 8) 0 2) DegreeOneSmallSpectrum1094.graph sourceMap1021=true := by decide +kernel
theorem fusedMap1021_checked : acceptsGraphIso
    (fused (graph core1021) (root 8) 0 2) DegreeOneSmallSpectrum1095.graph fusedMap1021=true := by decide +kernel
theorem certified1021 : Certified (graph core1021) (root 8) 0 2 :=
  of_native_maps core1021 DegreeOneSmallSpectrum1094.graph DegreeOneSmallSpectrum1095.graph
    sourceMap1021 fusedMap1021 sourceMap1021_checked fusedMap1021_checked
    DegreeOneSmallComparisons.comparison1021
#print axioms sourceMap1021_checked
#print axioms fusedMap1021_checked
#print axioms certified1021
def sourceMap1021swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1021swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1021swap_checked : acceptsGraphIso
    (source (graph core1021) (root 8) 2 0) DegreeOneSmallSpectrum1094.graph sourceMap1021swap=true := by decide +kernel
theorem fusedMap1021swap_checked : acceptsGraphIso
    (fused (graph core1021) (root 8) 2 0) DegreeOneSmallSpectrum1095.graph fusedMap1021swap=true := by decide +kernel
theorem certified1021swap : Certified (graph core1021) (root 8) 2 0 :=
  of_native_maps core1021 DegreeOneSmallSpectrum1094.graph DegreeOneSmallSpectrum1095.graph
    sourceMap1021swap fusedMap1021swap sourceMap1021swap_checked fusedMap1021swap_checked
    DegreeOneSmallComparisons.comparison1021
#print axioms sourceMap1021swap_checked
#print axioms fusedMap1021swap_checked
#print axioms certified1021swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
