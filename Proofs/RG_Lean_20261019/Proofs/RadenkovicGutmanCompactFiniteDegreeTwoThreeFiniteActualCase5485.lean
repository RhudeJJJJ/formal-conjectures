/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5485 : Family 5 := level5.get ⟨17,by decide⟩
def sourceMap5485 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 6) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12] (sourceLabel 5 0 5 v)
def fusedMap5485 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 0 5 v)
theorem sourceMap5485_checked : acceptsGraphIso
    (source (graph core5485) (root 5) 0 5) DegreeOneSmallSpectrum1301.graph sourceMap5485=true := by decide +kernel
theorem fusedMap5485_checked : acceptsGraphIso
    (fused (graph core5485) (root 5) 0 5) DegreeOneSmallSpectrum909.graph fusedMap5485=true := by decide +kernel
theorem certified5485 : Certified (graph core5485) (root 5) 0 5 :=
  of_native_maps core5485 DegreeOneSmallSpectrum1301.graph DegreeOneSmallSpectrum909.graph
    sourceMap5485 fusedMap5485 sourceMap5485_checked fusedMap5485_checked
    DegreeTwoThreeFiniteComparisons.comparison5485
#print axioms sourceMap5485_checked
#print axioms fusedMap5485_checked
#print axioms certified5485
def sourceMap5485swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,9,10,11,12,8] (sourceLabel 5 5 0 v)
def fusedMap5485swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 5 0 v)
theorem sourceMap5485swap_checked : acceptsGraphIso
    (source (graph core5485) (root 5) 5 0) DegreeOneSmallSpectrum1301.graph sourceMap5485swap=true := by decide +kernel
theorem fusedMap5485swap_checked : acceptsGraphIso
    (fused (graph core5485) (root 5) 5 0) DegreeOneSmallSpectrum909.graph fusedMap5485swap=true := by decide +kernel
theorem certified5485swap : Certified (graph core5485) (root 5) 5 0 :=
  of_native_maps core5485 DegreeOneSmallSpectrum1301.graph DegreeOneSmallSpectrum909.graph
    sourceMap5485swap fusedMap5485swap sourceMap5485swap_checked fusedMap5485swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5485
#print axioms sourceMap5485swap_checked
#print axioms fusedMap5485swap_checked
#print axioms certified5485swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
