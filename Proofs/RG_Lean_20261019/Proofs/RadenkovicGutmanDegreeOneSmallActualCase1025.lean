/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1025 : Family 8 := level8.get ⟨110,by decide⟩
def sourceMap1025 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1025 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1025_checked : acceptsGraphIso
    (source (graph core1025) (root 8) 0 2) DegreeOneSmallSpectrum1100.graph sourceMap1025=true := by decide +kernel
theorem fusedMap1025_checked : acceptsGraphIso
    (fused (graph core1025) (root 8) 0 2) DegreeOneSmallSpectrum1101.graph fusedMap1025=true := by decide +kernel
theorem certified1025 : Certified (graph core1025) (root 8) 0 2 :=
  of_native_maps core1025 DegreeOneSmallSpectrum1100.graph DegreeOneSmallSpectrum1101.graph
    sourceMap1025 fusedMap1025 sourceMap1025_checked fusedMap1025_checked
    DegreeOneSmallComparisons.comparison1025
#print axioms sourceMap1025_checked
#print axioms fusedMap1025_checked
#print axioms certified1025
def sourceMap1025swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1025swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1025swap_checked : acceptsGraphIso
    (source (graph core1025) (root 8) 2 0) DegreeOneSmallSpectrum1100.graph sourceMap1025swap=true := by decide +kernel
theorem fusedMap1025swap_checked : acceptsGraphIso
    (fused (graph core1025) (root 8) 2 0) DegreeOneSmallSpectrum1101.graph fusedMap1025swap=true := by decide +kernel
theorem certified1025swap : Certified (graph core1025) (root 8) 2 0 :=
  of_native_maps core1025 DegreeOneSmallSpectrum1100.graph DegreeOneSmallSpectrum1101.graph
    sourceMap1025swap fusedMap1025swap sourceMap1025swap_checked fusedMap1025swap_checked
    DegreeOneSmallComparisons.comparison1025
#print axioms sourceMap1025swap_checked
#print axioms fusedMap1025swap_checked
#print axioms certified1025swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
