/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3635 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3635 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (sourceLabel 2 0 7 v)
def fusedMap3635 : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11] (fusedLabel 2 0 7 v)
theorem sourceMap3635_checked : acceptsGraphIso
    (source (graph core3635) (root 2) 0 7) DegreeOneSmallSpectrum370.graph sourceMap3635=true := by decide +kernel
theorem fusedMap3635_checked : acceptsGraphIso
    (fused (graph core3635) (root 2) 0 7) DegreeOneSmallSpectrum378.graph fusedMap3635=true := by decide +kernel
theorem certified3635 : Certified (graph core3635) (root 2) 0 7 :=
  of_native_maps core3635 DegreeOneSmallSpectrum370.graph DegreeOneSmallSpectrum378.graph
    sourceMap3635 fusedMap3635 sourceMap3635_checked fusedMap3635_checked
    DegreeTwoThreeFiniteComparisons.comparison3635
#print axioms sourceMap3635_checked
#print axioms fusedMap3635_checked
#print axioms certified3635
def sourceMap3635swap : (Vertices 2 ⊕ Fin 8 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,4,5,2,1,0,7,8,9,10,11,6] (sourceLabel 2 7 0 v)
def fusedMap3635swap : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11] (fusedLabel 2 7 0 v)
theorem sourceMap3635swap_checked : acceptsGraphIso
    (source (graph core3635) (root 2) 7 0) DegreeOneSmallSpectrum370.graph sourceMap3635swap=true := by decide +kernel
theorem fusedMap3635swap_checked : acceptsGraphIso
    (fused (graph core3635) (root 2) 7 0) DegreeOneSmallSpectrum378.graph fusedMap3635swap=true := by decide +kernel
theorem certified3635swap : Certified (graph core3635) (root 2) 7 0 :=
  of_native_maps core3635 DegreeOneSmallSpectrum370.graph DegreeOneSmallSpectrum378.graph
    sourceMap3635swap fusedMap3635swap sourceMap3635swap_checked fusedMap3635swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3635
#print axioms sourceMap3635swap_checked
#print axioms fusedMap3635swap_checked
#print axioms certified3635swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
