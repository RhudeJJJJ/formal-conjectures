/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1296 : Family 9 := level9.get ⟨62,by decide⟩
def sourceMap1296 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,11,10,8,9] (sourceLabel 9 0 1 v)
def fusedMap1296 : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 0 1 v)
theorem sourceMap1296_checked : acceptsGraphIso
    (source (graph core1296) (root 9) 0 1) DegreeOneSmallSpectrum1271.graph sourceMap1296=true := by decide +kernel
theorem fusedMap1296_checked : acceptsGraphIso
    (fused (graph core1296) (root 9) 0 1) DegreeOneSmallSpectrum893.graph fusedMap1296=true := by decide +kernel
theorem certified1296 : Certified (graph core1296) (root 9) 0 1 :=
  of_native_maps core1296 DegreeOneSmallSpectrum1271.graph DegreeOneSmallSpectrum893.graph
    sourceMap1296 fusedMap1296 sourceMap1296_checked fusedMap1296_checked
    DegreeOneSmallComparisons.comparison1296
#print axioms sourceMap1296_checked
#print axioms fusedMap1296_checked
#print axioms certified1296
def sourceMap1296swap : (Vertices 9 ⊕ Fin 2 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,11,8,9,10] (sourceLabel 9 1 0 v)
def fusedMap1296swap : (Vertices 9 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (fusedLabel 9 1 0 v)
theorem sourceMap1296swap_checked : acceptsGraphIso
    (source (graph core1296) (root 9) 1 0) DegreeOneSmallSpectrum1271.graph sourceMap1296swap=true := by decide +kernel
theorem fusedMap1296swap_checked : acceptsGraphIso
    (fused (graph core1296) (root 9) 1 0) DegreeOneSmallSpectrum893.graph fusedMap1296swap=true := by decide +kernel
theorem certified1296swap : Certified (graph core1296) (root 9) 1 0 :=
  of_native_maps core1296 DegreeOneSmallSpectrum1271.graph DegreeOneSmallSpectrum893.graph
    sourceMap1296swap fusedMap1296swap sourceMap1296swap_checked fusedMap1296swap_checked
    DegreeOneSmallComparisons.comparison1296
#print axioms sourceMap1296swap_checked
#print axioms fusedMap1296swap_checked
#print axioms certified1296swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
