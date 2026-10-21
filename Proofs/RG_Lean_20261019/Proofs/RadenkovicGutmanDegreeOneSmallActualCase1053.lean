/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1053 : Family 8 := level8.get ⟨122,by decide⟩
def sourceMap1053 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1053 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1053_checked : acceptsGraphIso
    (source (graph core1053) (root 8) 0 2) DegreeOneSmallSpectrum1200.graph sourceMap1053=true := by decide +kernel
theorem fusedMap1053_checked : acceptsGraphIso
    (fused (graph core1053) (root 8) 0 2) DegreeOneSmallSpectrum1201.graph fusedMap1053=true := by decide +kernel
theorem certified1053 : Certified (graph core1053) (root 8) 0 2 :=
  of_native_maps core1053 DegreeOneSmallSpectrum1200.graph DegreeOneSmallSpectrum1201.graph
    sourceMap1053 fusedMap1053 sourceMap1053_checked fusedMap1053_checked
    DegreeOneSmallComparisons.comparison1053
#print axioms sourceMap1053_checked
#print axioms fusedMap1053_checked
#print axioms certified1053
def sourceMap1053swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1053swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1053swap_checked : acceptsGraphIso
    (source (graph core1053) (root 8) 2 0) DegreeOneSmallSpectrum1200.graph sourceMap1053swap=true := by decide +kernel
theorem fusedMap1053swap_checked : acceptsGraphIso
    (fused (graph core1053) (root 8) 2 0) DegreeOneSmallSpectrum1201.graph fusedMap1053swap=true := by decide +kernel
theorem certified1053swap : Certified (graph core1053) (root 8) 2 0 :=
  of_native_maps core1053 DegreeOneSmallSpectrum1200.graph DegreeOneSmallSpectrum1201.graph
    sourceMap1053swap fusedMap1053swap sourceMap1053swap_checked fusedMap1053swap_checked
    DegreeOneSmallComparisons.comparison1053
#print axioms sourceMap1053swap_checked
#print axioms fusedMap1053swap_checked
#print axioms certified1053swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
