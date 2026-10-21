/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1156 : Family 8 := level8.get ⟨197,by decide⟩
def sourceMap1156 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap1156 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap1156_checked : acceptsGraphIso
    (source (graph core1156) (root 8) 0 1) DegreeOneSmallSpectrum634.graph sourceMap1156=true := by decide +kernel
theorem fusedMap1156_checked : acceptsGraphIso
    (fused (graph core1156) (root 8) 0 1) DegreeOneSmallSpectrum635.graph fusedMap1156=true := by decide +kernel
theorem certified1156 : Certified (graph core1156) (root 8) 0 1 :=
  of_native_maps core1156 DegreeOneSmallSpectrum634.graph DegreeOneSmallSpectrum635.graph
    sourceMap1156 fusedMap1156 sourceMap1156_checked fusedMap1156_checked
    DegreeOneSmallComparisons.comparison1156
#print axioms sourceMap1156_checked
#print axioms fusedMap1156_checked
#print axioms certified1156
def sourceMap1156swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap1156swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap1156swap_checked : acceptsGraphIso
    (source (graph core1156) (root 8) 1 0) DegreeOneSmallSpectrum634.graph sourceMap1156swap=true := by decide +kernel
theorem fusedMap1156swap_checked : acceptsGraphIso
    (fused (graph core1156) (root 8) 1 0) DegreeOneSmallSpectrum635.graph fusedMap1156swap=true := by decide +kernel
theorem certified1156swap : Certified (graph core1156) (root 8) 1 0 :=
  of_native_maps core1156 DegreeOneSmallSpectrum634.graph DegreeOneSmallSpectrum635.graph
    sourceMap1156swap fusedMap1156swap sourceMap1156swap_checked fusedMap1156swap_checked
    DegreeOneSmallComparisons.comparison1156
#print axioms sourceMap1156swap_checked
#print axioms fusedMap1156swap_checked
#print axioms certified1156swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
