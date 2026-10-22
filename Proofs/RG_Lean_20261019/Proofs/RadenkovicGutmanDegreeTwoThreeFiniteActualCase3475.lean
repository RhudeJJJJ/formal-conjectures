/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3475 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3475 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 7) → Fin 11 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10] (sourceLabel 2 0 6 v)
def fusedMap3475 : (Vertices 2 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (fusedLabel 2 0 6 v)
theorem sourceMap3475_checked : acceptsGraphIso
    (source (graph core3475) (root 2) 0 6) DegreeOneSmallSpectrum175.graph sourceMap3475=true := by decide +kernel
theorem fusedMap3475_checked : acceptsGraphIso
    (fused (graph core3475) (root 2) 0 6) DegreeOneSmallSpectrum164.graph fusedMap3475=true := by decide +kernel
theorem certified3475 : Certified (graph core3475) (root 2) 0 6 :=
  of_native_maps core3475 DegreeOneSmallSpectrum175.graph DegreeOneSmallSpectrum164.graph
    sourceMap3475 fusedMap3475 sourceMap3475_checked fusedMap3475_checked
    DegreeTwoThreeFiniteComparisons.comparison3475
#print axioms sourceMap3475_checked
#print axioms fusedMap3475_checked
#print axioms certified3475
def sourceMap3475swap : (Vertices 2 ⊕ Fin 7 ⊕ Fin 1) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,7,8,9,10,6] (sourceLabel 2 6 0 v)
def fusedMap3475swap : (Vertices 2 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (fusedLabel 2 6 0 v)
theorem sourceMap3475swap_checked : acceptsGraphIso
    (source (graph core3475) (root 2) 6 0) DegreeOneSmallSpectrum175.graph sourceMap3475swap=true := by decide +kernel
theorem fusedMap3475swap_checked : acceptsGraphIso
    (fused (graph core3475) (root 2) 6 0) DegreeOneSmallSpectrum164.graph fusedMap3475swap=true := by decide +kernel
theorem certified3475swap : Certified (graph core3475) (root 2) 6 0 :=
  of_native_maps core3475 DegreeOneSmallSpectrum175.graph DegreeOneSmallSpectrum164.graph
    sourceMap3475swap fusedMap3475swap sourceMap3475swap_checked fusedMap3475swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3475
#print axioms sourceMap3475swap_checked
#print axioms fusedMap3475swap_checked
#print axioms certified3475swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
