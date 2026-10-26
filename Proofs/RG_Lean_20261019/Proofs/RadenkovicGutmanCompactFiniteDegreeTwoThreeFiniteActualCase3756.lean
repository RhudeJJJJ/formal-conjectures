/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3756 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3756 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,3,4,1,2,5,6,7] (sourceLabel 2 1 2 v)
def fusedMap3756 : (Vertices 2 ⊕ Fin 5) → Fin 8 :=
  fun v => ![2,3,4,1,0,5,6,7] (fusedLabel 2 1 2 v)
theorem sourceMap3756_checked : acceptsGraphIso
    (source (graph core3756) (root 2) 1 2) DegreeOneSmallSpectrum023.graph sourceMap3756=true := by decide +kernel
theorem fusedMap3756_checked : acceptsGraphIso
    (fused (graph core3756) (root 2) 1 2) DegreeOneSmallSpectrum021.graph fusedMap3756=true := by decide +kernel
theorem certified3756 : Certified (graph core3756) (root 2) 1 2 :=
  of_native_maps core3756 DegreeOneSmallSpectrum023.graph DegreeOneSmallSpectrum021.graph
    sourceMap3756 fusedMap3756 sourceMap3756_checked fusedMap3756_checked
    DegreeTwoThreeFiniteComparisons.comparison3756
#print axioms sourceMap3756_checked
#print axioms fusedMap3756_checked
#print axioms certified3756
def sourceMap3756swap : (Vertices 2 ⊕ Fin 3 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,3,4,5,6,7,1,2] (sourceLabel 2 2 1 v)
def fusedMap3756swap : (Vertices 2 ⊕ Fin 5) → Fin 8 :=
  fun v => ![2,3,4,1,0,5,6,7] (fusedLabel 2 2 1 v)
theorem sourceMap3756swap_checked : acceptsGraphIso
    (source (graph core3756) (root 2) 2 1) DegreeOneSmallSpectrum023.graph sourceMap3756swap=true := by decide +kernel
theorem fusedMap3756swap_checked : acceptsGraphIso
    (fused (graph core3756) (root 2) 2 1) DegreeOneSmallSpectrum021.graph fusedMap3756swap=true := by decide +kernel
theorem certified3756swap : Certified (graph core3756) (root 2) 2 1 :=
  of_native_maps core3756 DegreeOneSmallSpectrum023.graph DegreeOneSmallSpectrum021.graph
    sourceMap3756swap fusedMap3756swap sourceMap3756swap_checked fusedMap3756swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3756
#print axioms sourceMap3756swap_checked
#print axioms fusedMap3756swap_checked
#print axioms certified3756swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
