/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3085 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap3085 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap3085 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap3085_checked : acceptsGraphIso
    (source (graph core3085) (root 5) 0 5) DegreeOneSmallSpectrum1021.graph sourceMap3085=true := by decide +kernel
theorem fusedMap3085_checked : acceptsGraphIso
    (fused (graph core3085) (root 5) 0 5) DegreeOneSmallSpectrum863.graph fusedMap3085=true := by decide +kernel
theorem certified3085 : Certified (graph core3085) (root 5) 0 5 :=
  of_native_maps core3085 DegreeOneSmallSpectrum1021.graph DegreeOneSmallSpectrum863.graph
    sourceMap3085 fusedMap3085 sourceMap3085_checked fusedMap3085_checked
    DegreeTwoThreeFiniteComparisons.comparison3085
#print axioms sourceMap3085_checked
#print axioms fusedMap3085_checked
#print axioms certified3085
def sourceMap3085swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,8] (sourceLabel 5 5 0 v)
def fusedMap3085swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap3085swap_checked : acceptsGraphIso
    (source (graph core3085) (root 5) 5 0) DegreeOneSmallSpectrum1021.graph sourceMap3085swap=true := by decide +kernel
theorem fusedMap3085swap_checked : acceptsGraphIso
    (fused (graph core3085) (root 5) 5 0) DegreeOneSmallSpectrum863.graph fusedMap3085swap=true := by decide +kernel
theorem certified3085swap : Certified (graph core3085) (root 5) 5 0 :=
  of_native_maps core3085 DegreeOneSmallSpectrum1021.graph DegreeOneSmallSpectrum863.graph
    sourceMap3085swap fusedMap3085swap sourceMap3085swap_checked fusedMap3085swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3085
#print axioms sourceMap3085swap_checked
#print axioms fusedMap3085swap_checked
#print axioms certified3085swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
