/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1101 : Family 8 := level8.get ⟨150,by decide⟩
def sourceMap1101 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1101 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1101_checked : acceptsGraphIso
    (source (graph core1101) (root 8) 0 2) DegreeOneSmallSpectrum1402.graph sourceMap1101=true := by decide +kernel
theorem fusedMap1101_checked : acceptsGraphIso
    (fused (graph core1101) (root 8) 0 2) DegreeOneSmallSpectrum1403.graph fusedMap1101=true := by decide +kernel
theorem certified1101 : Certified (graph core1101) (root 8) 0 2 :=
  of_native_maps core1101 DegreeOneSmallSpectrum1402.graph DegreeOneSmallSpectrum1403.graph
    sourceMap1101 fusedMap1101 sourceMap1101_checked fusedMap1101_checked
    DegreeOneSmallComparisons.comparison1101
#print axioms sourceMap1101_checked
#print axioms fusedMap1101_checked
#print axioms certified1101
def sourceMap1101swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1101swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1101swap_checked : acceptsGraphIso
    (source (graph core1101) (root 8) 2 0) DegreeOneSmallSpectrum1402.graph sourceMap1101swap=true := by decide +kernel
theorem fusedMap1101swap_checked : acceptsGraphIso
    (fused (graph core1101) (root 8) 2 0) DegreeOneSmallSpectrum1403.graph fusedMap1101swap=true := by decide +kernel
theorem certified1101swap : Certified (graph core1101) (root 8) 2 0 :=
  of_native_maps core1101 DegreeOneSmallSpectrum1402.graph DegreeOneSmallSpectrum1403.graph
    sourceMap1101swap fusedMap1101swap sourceMap1101swap_checked fusedMap1101swap_checked
    DegreeOneSmallComparisons.comparison1101
#print axioms sourceMap1101swap_checked
#print axioms fusedMap1101swap_checked
#print axioms certified1101swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
