/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1117 : Family 8 := level8.get ⟨163,by decide⟩
def sourceMap1117 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1117 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1117_checked : acceptsGraphIso
    (source (graph core1117) (root 8) 0 2) DegreeOneSmallSpectrum1466.graph sourceMap1117=true := by decide +kernel
theorem fusedMap1117_checked : acceptsGraphIso
    (fused (graph core1117) (root 8) 0 2) DegreeOneSmallSpectrum1467.graph fusedMap1117=true := by decide +kernel
theorem certified1117 : Certified (graph core1117) (root 8) 0 2 :=
  of_native_maps core1117 DegreeOneSmallSpectrum1466.graph DegreeOneSmallSpectrum1467.graph
    sourceMap1117 fusedMap1117 sourceMap1117_checked fusedMap1117_checked
    DegreeOneSmallComparisons.comparison1117
#print axioms sourceMap1117_checked
#print axioms fusedMap1117_checked
#print axioms certified1117
def sourceMap1117swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1117swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1117swap_checked : acceptsGraphIso
    (source (graph core1117) (root 8) 2 0) DegreeOneSmallSpectrum1466.graph sourceMap1117swap=true := by decide +kernel
theorem fusedMap1117swap_checked : acceptsGraphIso
    (fused (graph core1117) (root 8) 2 0) DegreeOneSmallSpectrum1467.graph fusedMap1117swap=true := by decide +kernel
theorem certified1117swap : Certified (graph core1117) (root 8) 2 0 :=
  of_native_maps core1117 DegreeOneSmallSpectrum1466.graph DegreeOneSmallSpectrum1467.graph
    sourceMap1117swap fusedMap1117swap sourceMap1117swap_checked fusedMap1117swap_checked
    DegreeOneSmallComparisons.comparison1117
#print axioms sourceMap1117swap_checked
#print axioms fusedMap1117swap_checked
#print axioms certified1117swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
