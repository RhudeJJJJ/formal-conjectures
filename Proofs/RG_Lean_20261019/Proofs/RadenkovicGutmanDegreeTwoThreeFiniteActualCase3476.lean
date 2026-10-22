/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3476 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap3476 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (sourceLabel 3 0 6 v)
def fusedMap3476 : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 0 6 v)
theorem sourceMap3476_checked : acceptsGraphIso
    (source (graph core3476) (root 3) 0 6) DegreeOneSmallSpectrum380.graph sourceMap3476=true := by decide +kernel
theorem fusedMap3476_checked : acceptsGraphIso
    (fused (graph core3476) (root 3) 0 6) DegreeOneSmallSpectrum386.graph fusedMap3476=true := by decide +kernel
theorem certified3476 : Certified (graph core3476) (root 3) 0 6 :=
  of_native_maps core3476 DegreeOneSmallSpectrum380.graph DegreeOneSmallSpectrum386.graph
    sourceMap3476 fusedMap3476 sourceMap3476_checked fusedMap3476_checked
    DegreeTwoThreeFiniteComparisons.comparison3476
#print axioms sourceMap3476_checked
#print axioms fusedMap3476_checked
#print axioms certified3476
def sourceMap3476swap : (Vertices 3 ⊕ Fin 7 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,3,4,5,1,0,7,8,9,10,11,6] (sourceLabel 3 6 0 v)
def fusedMap3476swap : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 6 0 v)
theorem sourceMap3476swap_checked : acceptsGraphIso
    (source (graph core3476) (root 3) 6 0) DegreeOneSmallSpectrum380.graph sourceMap3476swap=true := by decide +kernel
theorem fusedMap3476swap_checked : acceptsGraphIso
    (fused (graph core3476) (root 3) 6 0) DegreeOneSmallSpectrum386.graph fusedMap3476swap=true := by decide +kernel
theorem certified3476swap : Certified (graph core3476) (root 3) 6 0 :=
  of_native_maps core3476 DegreeOneSmallSpectrum380.graph DegreeOneSmallSpectrum386.graph
    sourceMap3476swap fusedMap3476swap sourceMap3476swap_checked fusedMap3476swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3476
#print axioms sourceMap3476swap_checked
#print axioms fusedMap3476swap_checked
#print axioms certified3476swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
