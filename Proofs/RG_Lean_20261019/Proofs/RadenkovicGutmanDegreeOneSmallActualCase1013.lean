/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1013 : Family 8 := level8.get ⟨104,by decide⟩
def sourceMap1013 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1013 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1013_checked : acceptsGraphIso
    (source (graph core1013) (root 8) 0 2) DegreeOneSmallSpectrum1048.graph sourceMap1013=true := by decide +kernel
theorem fusedMap1013_checked : acceptsGraphIso
    (fused (graph core1013) (root 8) 0 2) DegreeOneSmallSpectrum1049.graph fusedMap1013=true := by decide +kernel
theorem certified1013 : Certified (graph core1013) (root 8) 0 2 :=
  of_native_maps core1013 DegreeOneSmallSpectrum1048.graph DegreeOneSmallSpectrum1049.graph
    sourceMap1013 fusedMap1013 sourceMap1013_checked fusedMap1013_checked
    DegreeOneSmallComparisons.comparison1013
#print axioms sourceMap1013_checked
#print axioms fusedMap1013_checked
#print axioms certified1013
def sourceMap1013swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1013swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1013swap_checked : acceptsGraphIso
    (source (graph core1013) (root 8) 2 0) DegreeOneSmallSpectrum1048.graph sourceMap1013swap=true := by decide +kernel
theorem fusedMap1013swap_checked : acceptsGraphIso
    (fused (graph core1013) (root 8) 2 0) DegreeOneSmallSpectrum1049.graph fusedMap1013swap=true := by decide +kernel
theorem certified1013swap : Certified (graph core1013) (root 8) 2 0 :=
  of_native_maps core1013 DegreeOneSmallSpectrum1048.graph DegreeOneSmallSpectrum1049.graph
    sourceMap1013swap fusedMap1013swap sourceMap1013swap_checked fusedMap1013swap_checked
    DegreeOneSmallComparisons.comparison1013
#print axioms sourceMap1013swap_checked
#print axioms fusedMap1013swap_checked
#print axioms certified1013swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
