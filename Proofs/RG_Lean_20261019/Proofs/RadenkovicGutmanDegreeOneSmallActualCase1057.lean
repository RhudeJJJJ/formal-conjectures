/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1057 : Family 8 := level8.get ⟨124,by decide⟩
def sourceMap1057 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1057 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap1057_checked : acceptsGraphIso
    (source (graph core1057) (root 8) 0 2) DegreeOneSmallSpectrum1215.graph sourceMap1057=true := by decide +kernel
theorem fusedMap1057_checked : acceptsGraphIso
    (fused (graph core1057) (root 8) 0 2) DegreeOneSmallSpectrum1216.graph fusedMap1057=true := by decide +kernel
theorem certified1057 : Certified (graph core1057) (root 8) 0 2 :=
  of_native_maps core1057 DegreeOneSmallSpectrum1215.graph DegreeOneSmallSpectrum1216.graph
    sourceMap1057 fusedMap1057 sourceMap1057_checked fusedMap1057_checked
    DegreeOneSmallComparisons.comparison1057
#print axioms sourceMap1057_checked
#print axioms fusedMap1057_checked
#print axioms certified1057
def sourceMap1057swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1057swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap1057swap_checked : acceptsGraphIso
    (source (graph core1057) (root 8) 2 0) DegreeOneSmallSpectrum1215.graph sourceMap1057swap=true := by decide +kernel
theorem fusedMap1057swap_checked : acceptsGraphIso
    (fused (graph core1057) (root 8) 2 0) DegreeOneSmallSpectrum1216.graph fusedMap1057swap=true := by decide +kernel
theorem certified1057swap : Certified (graph core1057) (root 8) 2 0 :=
  of_native_maps core1057 DegreeOneSmallSpectrum1215.graph DegreeOneSmallSpectrum1216.graph
    sourceMap1057swap fusedMap1057swap sourceMap1057swap_checked fusedMap1057swap_checked
    DegreeOneSmallComparisons.comparison1057
#print axioms sourceMap1057swap_checked
#print axioms fusedMap1057swap_checked
#print axioms certified1057swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
