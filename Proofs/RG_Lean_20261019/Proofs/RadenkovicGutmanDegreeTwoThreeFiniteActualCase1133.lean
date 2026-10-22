/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1133 : Family 8 := level8.get ⟨128,by decide⟩
def sourceMap1133 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,6,7,8,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap1133 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (fusedLabel 8 0 2 v)
theorem sourceMap1133_checked : acceptsGraphIso
    (source (graph core1133) (root 8) 0 2) DegreeOneSmallSpectrum1274.graph sourceMap1133=true := by decide +kernel
theorem fusedMap1133_checked : acceptsGraphIso
    (fused (graph core1133) (root 8) 0 2) DegreeOneSmallSpectrum1288.graph fusedMap1133=true := by decide +kernel
theorem certified1133 : Certified (graph core1133) (root 8) 0 2 :=
  of_native_maps core1133 DegreeOneSmallSpectrum1274.graph DegreeOneSmallSpectrum1288.graph
    sourceMap1133 fusedMap1133 sourceMap1133_checked fusedMap1133_checked
    DegreeTwoThreeFiniteComparisons.comparison1133
#print axioms sourceMap1133_checked
#print axioms fusedMap1133_checked
#print axioms certified1133
def sourceMap1133swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap1133swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,10,11,12,6,7,8,9] (fusedLabel 8 2 0 v)
theorem sourceMap1133swap_checked : acceptsGraphIso
    (source (graph core1133) (root 8) 2 0) DegreeOneSmallSpectrum1274.graph sourceMap1133swap=true := by decide +kernel
theorem fusedMap1133swap_checked : acceptsGraphIso
    (fused (graph core1133) (root 8) 2 0) DegreeOneSmallSpectrum1288.graph fusedMap1133swap=true := by decide +kernel
theorem certified1133swap : Certified (graph core1133) (root 8) 2 0 :=
  of_native_maps core1133 DegreeOneSmallSpectrum1274.graph DegreeOneSmallSpectrum1288.graph
    sourceMap1133swap fusedMap1133swap sourceMap1133swap_checked fusedMap1133swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1133
#print axioms sourceMap1133swap_checked
#print axioms fusedMap1133swap_checked
#print axioms certified1133swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
