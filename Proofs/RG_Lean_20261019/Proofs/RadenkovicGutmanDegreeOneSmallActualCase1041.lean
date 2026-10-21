/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1041 : Family 8 := level8.get ⟨116,by decide⟩
def sourceMap1041 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1041 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1041_checked : acceptsGraphIso
    (source (graph core1041) (root 8) 0 2) DegreeOneSmallSpectrum1146.graph sourceMap1041=true := by decide +kernel
theorem fusedMap1041_checked : acceptsGraphIso
    (fused (graph core1041) (root 8) 0 2) DegreeOneSmallSpectrum1147.graph fusedMap1041=true := by decide +kernel
theorem certified1041 : Certified (graph core1041) (root 8) 0 2 :=
  of_native_maps core1041 DegreeOneSmallSpectrum1146.graph DegreeOneSmallSpectrum1147.graph
    sourceMap1041 fusedMap1041 sourceMap1041_checked fusedMap1041_checked
    DegreeOneSmallComparisons.comparison1041
#print axioms sourceMap1041_checked
#print axioms fusedMap1041_checked
#print axioms certified1041
def sourceMap1041swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1041swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1041swap_checked : acceptsGraphIso
    (source (graph core1041) (root 8) 2 0) DegreeOneSmallSpectrum1146.graph sourceMap1041swap=true := by decide +kernel
theorem fusedMap1041swap_checked : acceptsGraphIso
    (fused (graph core1041) (root 8) 2 0) DegreeOneSmallSpectrum1147.graph fusedMap1041swap=true := by decide +kernel
theorem certified1041swap : Certified (graph core1041) (root 8) 2 0 :=
  of_native_maps core1041 DegreeOneSmallSpectrum1146.graph DegreeOneSmallSpectrum1147.graph
    sourceMap1041swap fusedMap1041swap sourceMap1041swap_checked fusedMap1041swap_checked
    DegreeOneSmallComparisons.comparison1041
#print axioms sourceMap1041swap_checked
#print axioms fusedMap1041swap_checked
#print axioms certified1041swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
