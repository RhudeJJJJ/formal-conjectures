/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1324 : Family 9 := level9.get ⟨82,by decide⟩
def sourceMap1324 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 9 0 1 v)
def fusedMap1324 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1324_checked : acceptsGraphIso
    (source (graph core1324) (root 9) 0 1) DegreeOneSmallSpectrum1425.graph sourceMap1324=true := by decide +kernel
theorem fusedMap1324_checked : acceptsGraphIso
    (fused (graph core1324) (root 9) 0 1) DegreeOneSmallSpectrum928.graph fusedMap1324=true := by decide +kernel
theorem certified1324 : Certified (graph core1324) (root 9) 0 1 :=
  of_native_maps core1324 DegreeOneSmallSpectrum1425.graph DegreeOneSmallSpectrum928.graph
    sourceMap1324 fusedMap1324 sourceMap1324_checked fusedMap1324_checked
    DegreeOneSmallComparisons.comparison1324
#print axioms sourceMap1324_checked
#print axioms fusedMap1324_checked
#print axioms certified1324
def sourceMap1324swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 9 1 0 v)
def fusedMap1324swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1324swap_checked : acceptsGraphIso
    (source (graph core1324) (root 9) 1 0) DegreeOneSmallSpectrum1425.graph sourceMap1324swap=true := by decide +kernel
theorem fusedMap1324swap_checked : acceptsGraphIso
    (fused (graph core1324) (root 9) 1 0) DegreeOneSmallSpectrum928.graph fusedMap1324swap=true := by decide +kernel
theorem certified1324swap : Certified (graph core1324) (root 9) 1 0 :=
  of_native_maps core1324 DegreeOneSmallSpectrum1425.graph DegreeOneSmallSpectrum928.graph
    sourceMap1324swap fusedMap1324swap sourceMap1324swap_checked fusedMap1324swap_checked
    DegreeOneSmallComparisons.comparison1324
#print axioms sourceMap1324swap_checked
#print axioms fusedMap1324swap_checked
#print axioms certified1324swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
