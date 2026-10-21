/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1270 : Family 9 := level9.get ⟨46,by decide⟩
def sourceMap1270 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (sourceLabel 9 0 1 v)
def fusedMap1270 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 0 1 v)
theorem sourceMap1270_checked : acceptsGraphIso
    (source (graph core1270) (root 9) 0 1) DegreeOneSmallSpectrum1073.graph sourceMap1270=true := by decide +kernel
theorem fusedMap1270_checked : acceptsGraphIso
    (fused (graph core1270) (root 9) 0 1) DegreeOneSmallSpectrum865.graph fusedMap1270=true := by decide +kernel
theorem certified1270 : Certified (graph core1270) (root 9) 0 1 :=
  of_native_maps core1270 DegreeOneSmallSpectrum1073.graph DegreeOneSmallSpectrum865.graph
    sourceMap1270 fusedMap1270 sourceMap1270_checked fusedMap1270_checked
    DegreeOneSmallComparisons.comparison1270
#print axioms sourceMap1270_checked
#print axioms fusedMap1270_checked
#print axioms certified1270
def sourceMap1270swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 9 1 0 v)
def fusedMap1270swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (fusedLabel 9 1 0 v)
theorem sourceMap1270swap_checked : acceptsGraphIso
    (source (graph core1270) (root 9) 1 0) DegreeOneSmallSpectrum1073.graph sourceMap1270swap=true := by decide +kernel
theorem fusedMap1270swap_checked : acceptsGraphIso
    (fused (graph core1270) (root 9) 1 0) DegreeOneSmallSpectrum865.graph fusedMap1270swap=true := by decide +kernel
theorem certified1270swap : Certified (graph core1270) (root 9) 1 0 :=
  of_native_maps core1270 DegreeOneSmallSpectrum1073.graph DegreeOneSmallSpectrum865.graph
    sourceMap1270swap fusedMap1270swap sourceMap1270swap_checked fusedMap1270swap_checked
    DegreeOneSmallComparisons.comparison1270
#print axioms sourceMap1270swap_checked
#print axioms fusedMap1270swap_checked
#print axioms certified1270swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
