/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons22
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1142 : Family 8 := level8.get ⟨154,by decide⟩
def sourceMap1142 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap1142 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 0 2 v)
theorem sourceMap1142_checked : acceptsGraphIso
    (source (graph core1142) (root 8) 0 2) DegreeOneSmallSpectrum1422.graph sourceMap1142=true := by decide +kernel
theorem fusedMap1142_checked : acceptsGraphIso
    (fused (graph core1142) (root 8) 0 2) DegreeOneSmallSpectrum1424.graph fusedMap1142=true := by decide +kernel
theorem certified1142 : Certified (graph core1142) (root 8) 0 2 :=
  of_native_maps core1142 DegreeOneSmallSpectrum1422.graph DegreeOneSmallSpectrum1424.graph
    sourceMap1142 fusedMap1142 sourceMap1142_checked fusedMap1142_checked
    DegreeTwoThreeFiniteComparisons.comparison1142
#print axioms sourceMap1142_checked
#print axioms fusedMap1142_checked
#print axioms certified1142
def sourceMap1142swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10,12] (sourceLabel 8 2 0 v)
def fusedMap1142swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (fusedLabel 8 2 0 v)
theorem sourceMap1142swap_checked : acceptsGraphIso
    (source (graph core1142) (root 8) 2 0) DegreeOneSmallSpectrum1422.graph sourceMap1142swap=true := by decide +kernel
theorem fusedMap1142swap_checked : acceptsGraphIso
    (fused (graph core1142) (root 8) 2 0) DegreeOneSmallSpectrum1424.graph fusedMap1142swap=true := by decide +kernel
theorem certified1142swap : Certified (graph core1142) (root 8) 2 0 :=
  of_native_maps core1142 DegreeOneSmallSpectrum1422.graph DegreeOneSmallSpectrum1424.graph
    sourceMap1142swap fusedMap1142swap sourceMap1142swap_checked fusedMap1142swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1142
#print axioms sourceMap1142swap_checked
#print axioms fusedMap1142swap_checked
#print axioms certified1142swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
