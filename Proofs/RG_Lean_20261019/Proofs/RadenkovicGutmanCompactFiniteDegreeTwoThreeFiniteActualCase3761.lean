/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3761 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3761 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,4,5,2,3,0,6,7,8] (sourceLabel 2 1 3 v)
def fusedMap3761 : (Vertices 2 ⊕ Fin 6) → Fin 9 :=
  fun v => ![2,3,4,1,0,5,6,7,8] (fusedLabel 2 1 3 v)
theorem sourceMap3761_checked : acceptsGraphIso
    (source (graph core3761) (root 2) 1 3) DegreeOneSmallSpectrum058.graph sourceMap3761=true := by decide +kernel
theorem fusedMap3761_checked : acceptsGraphIso
    (fused (graph core3761) (root 2) 1 3) DegreeOneSmallSpectrum034.graph fusedMap3761=true := by decide +kernel
theorem certified3761 : Certified (graph core3761) (root 2) 1 3 :=
  of_native_maps core3761 DegreeOneSmallSpectrum058.graph DegreeOneSmallSpectrum034.graph
    sourceMap3761 fusedMap3761 sourceMap3761_checked fusedMap3761_checked
    DegreeTwoThreeFiniteComparisons.comparison3761
#print axioms sourceMap3761_checked
#print axioms fusedMap3761_checked
#print axioms certified3761
def sourceMap3761swap : (Vertices 2 ⊕ Fin 4 ⊕ Fin 2) → Fin 9 :=
  fun v => ![1,4,5,0,6,7,8,2,3] (sourceLabel 2 3 1 v)
def fusedMap3761swap : (Vertices 2 ⊕ Fin 6) → Fin 9 :=
  fun v => ![2,3,4,1,0,5,6,7,8] (fusedLabel 2 3 1 v)
theorem sourceMap3761swap_checked : acceptsGraphIso
    (source (graph core3761) (root 2) 3 1) DegreeOneSmallSpectrum058.graph sourceMap3761swap=true := by decide +kernel
theorem fusedMap3761swap_checked : acceptsGraphIso
    (fused (graph core3761) (root 2) 3 1) DegreeOneSmallSpectrum034.graph fusedMap3761swap=true := by decide +kernel
theorem certified3761swap : Certified (graph core3761) (root 2) 3 1 :=
  of_native_maps core3761 DegreeOneSmallSpectrum058.graph DegreeOneSmallSpectrum034.graph
    sourceMap3761swap fusedMap3761swap sourceMap3761swap_checked fusedMap3761swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3761
#print axioms sourceMap3761swap_checked
#print axioms fusedMap3761swap_checked
#print axioms certified3761swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
