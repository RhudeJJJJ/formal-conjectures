/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0071 : Family 8 := level8.get ⟨38,by decide⟩
def sourceMap0071 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0071 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0071_checked : acceptsGraphIso
    (source (graph core0071) (root 8) 0 0) DegreeTwoThreeSpectrum236.graph sourceMap0071=true := by decide +kernel
theorem fusedMap0071_checked : acceptsGraphIso
    (fused (graph core0071) (root 8) 0 0) DegreeOneSmallSpectrum173.graph fusedMap0071=true := by decide +kernel
theorem certified0071 : Certified (graph core0071) (root 8) 0 0 :=
  of_native_maps core0071 DegreeTwoThreeSpectrum236.graph DegreeOneSmallSpectrum173.graph
    sourceMap0071 fusedMap0071 sourceMap0071_checked fusedMap0071_checked
    DegreeTwoThreeFiniteComparisons.comparison0071
#print axioms sourceMap0071_checked
#print axioms fusedMap0071_checked
#print axioms certified0071
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
