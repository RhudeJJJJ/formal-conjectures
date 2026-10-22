/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1137 : Family 8 := level8.get ⟨139,by decide⟩
def sourceMap1137 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 8 0 2 v)
def fusedMap1137 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 0 2 v)
theorem sourceMap1137_checked : acceptsGraphIso
    (source (graph core1137) (root 8) 0 2) DegreeOneSmallSpectrum1342.graph sourceMap1137=true := by decide +kernel
theorem fusedMap1137_checked : acceptsGraphIso
    (fused (graph core1137) (root 8) 0 2) DegreeOneSmallSpectrum1347.graph fusedMap1137=true := by decide +kernel
theorem certified1137 : Certified (graph core1137) (root 8) 0 2 :=
  of_native_maps core1137 DegreeOneSmallSpectrum1342.graph DegreeOneSmallSpectrum1347.graph
    sourceMap1137 fusedMap1137 sourceMap1137_checked fusedMap1137_checked
    DegreeTwoThreeFiniteComparisons.comparison1137
#print axioms sourceMap1137_checked
#print axioms fusedMap1137_checked
#print axioms certified1137
def sourceMap1137swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9,12] (sourceLabel 8 2 0 v)
def fusedMap1137swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (fusedLabel 8 2 0 v)
theorem sourceMap1137swap_checked : acceptsGraphIso
    (source (graph core1137) (root 8) 2 0) DegreeOneSmallSpectrum1342.graph sourceMap1137swap=true := by decide +kernel
theorem fusedMap1137swap_checked : acceptsGraphIso
    (fused (graph core1137) (root 8) 2 0) DegreeOneSmallSpectrum1347.graph fusedMap1137swap=true := by decide +kernel
theorem certified1137swap : Certified (graph core1137) (root 8) 2 0 :=
  of_native_maps core1137 DegreeOneSmallSpectrum1342.graph DegreeOneSmallSpectrum1347.graph
    sourceMap1137swap fusedMap1137swap sourceMap1137swap_checked fusedMap1137swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1137
#print axioms sourceMap1137swap_checked
#print axioms fusedMap1137swap_checked
#print axioms certified1137swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
