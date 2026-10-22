/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3076 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3076 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (sourceLabel 2 0 5 v)
def fusedMap3076 : (Vertices 2 ⊕ Fin 7) → Fin 10 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9] (fusedLabel 2 0 5 v)
theorem sourceMap3076_checked : acceptsGraphIso
    (source (graph core3076) (root 2) 0 5) DegreeOneSmallSpectrum074.graph sourceMap3076=true := by decide +kernel
theorem fusedMap3076_checked : acceptsGraphIso
    (fused (graph core3076) (root 2) 0 5) DegreeOneSmallSpectrum080.graph fusedMap3076=true := by decide +kernel
theorem certified3076 : Certified (graph core3076) (root 2) 0 5 :=
  of_native_maps core3076 DegreeOneSmallSpectrum074.graph DegreeOneSmallSpectrum080.graph
    sourceMap3076 fusedMap3076 sourceMap3076_checked fusedMap3076_checked
    DegreeTwoThreeFiniteComparisons.comparison3076
#print axioms sourceMap3076_checked
#print axioms fusedMap3076_checked
#print axioms certified3076
def sourceMap3076swap : (Vertices 2 ⊕ Fin 6 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,3,4,1,0,6,7,8,9,5] (sourceLabel 2 5 0 v)
def fusedMap3076swap : (Vertices 2 ⊕ Fin 7) → Fin 10 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9] (fusedLabel 2 5 0 v)
theorem sourceMap3076swap_checked : acceptsGraphIso
    (source (graph core3076) (root 2) 5 0) DegreeOneSmallSpectrum074.graph sourceMap3076swap=true := by decide +kernel
theorem fusedMap3076swap_checked : acceptsGraphIso
    (fused (graph core3076) (root 2) 5 0) DegreeOneSmallSpectrum080.graph fusedMap3076swap=true := by decide +kernel
theorem certified3076swap : Certified (graph core3076) (root 2) 5 0 :=
  of_native_maps core3076 DegreeOneSmallSpectrum074.graph DegreeOneSmallSpectrum080.graph
    sourceMap3076swap fusedMap3076swap sourceMap3076swap_checked fusedMap3076swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3076
#print axioms sourceMap3076swap_checked
#print axioms fusedMap3076swap_checked
#print axioms certified3076swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
