/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3086 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap3086 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap3086 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap3086_checked : acceptsGraphIso
    (source (graph core3086) (root 5) 0 5) DegreeOneSmallSpectrum1095.graph sourceMap3086=true := by decide +kernel
theorem fusedMap3086_checked : acceptsGraphIso
    (fused (graph core3086) (root 5) 0 5) DegreeOneSmallSpectrum871.graph fusedMap3086=true := by decide +kernel
theorem certified3086 : Certified (graph core3086) (root 5) 0 5 :=
  of_native_maps core3086 DegreeOneSmallSpectrum1095.graph DegreeOneSmallSpectrum871.graph
    sourceMap3086 fusedMap3086 sourceMap3086_checked fusedMap3086_checked
    DegreeTwoThreeFiniteComparisons.comparison3086
#print axioms sourceMap3086_checked
#print axioms fusedMap3086_checked
#print axioms certified3086
def sourceMap3086swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,8] (sourceLabel 5 5 0 v)
def fusedMap3086swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap3086swap_checked : acceptsGraphIso
    (source (graph core3086) (root 5) 5 0) DegreeOneSmallSpectrum1095.graph sourceMap3086swap=true := by decide +kernel
theorem fusedMap3086swap_checked : acceptsGraphIso
    (fused (graph core3086) (root 5) 5 0) DegreeOneSmallSpectrum871.graph fusedMap3086swap=true := by decide +kernel
theorem certified3086swap : Certified (graph core3086) (root 5) 5 0 :=
  of_native_maps core3086 DegreeOneSmallSpectrum1095.graph DegreeOneSmallSpectrum871.graph
    sourceMap3086swap fusedMap3086swap sourceMap3086swap_checked fusedMap3086swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3086
#print axioms sourceMap3086swap_checked
#print axioms fusedMap3086swap_checked
#print axioms certified3086swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
