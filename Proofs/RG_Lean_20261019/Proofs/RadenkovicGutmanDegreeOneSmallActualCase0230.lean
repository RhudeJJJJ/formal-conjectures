/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0230 : Family 5 := level5.get ⟨6,by decide⟩
def sourceMap0230 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 5 2 3 v)
def fusedMap0230 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 2 3 v)
theorem sourceMap0230_checked : acceptsGraphIso
    (source (graph core0230) (root 5) 2 3) DegreeOneSmallSpectrum1136.graph sourceMap0230=true := by decide +kernel
theorem fusedMap0230_checked : acceptsGraphIso
    (fused (graph core0230) (root 5) 2 3) DegreeOneSmallSpectrum879.graph fusedMap0230=true := by decide +kernel
theorem certified0230 : Certified (graph core0230) (root 5) 2 3 :=
  of_native_maps core0230 DegreeOneSmallSpectrum1136.graph DegreeOneSmallSpectrum879.graph
    sourceMap0230 fusedMap0230 sourceMap0230_checked fusedMap0230_checked
    DegreeOneSmallComparisons.comparison0230
#print axioms sourceMap0230_checked
#print axioms fusedMap0230_checked
#print axioms certified0230
def sourceMap0230swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,6,7,8] (sourceLabel 5 3 2 v)
def fusedMap0230swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 3 2 v)
theorem sourceMap0230swap_checked : acceptsGraphIso
    (source (graph core0230) (root 5) 3 2) DegreeOneSmallSpectrum1136.graph sourceMap0230swap=true := by decide +kernel
theorem fusedMap0230swap_checked : acceptsGraphIso
    (fused (graph core0230) (root 5) 3 2) DegreeOneSmallSpectrum879.graph fusedMap0230swap=true := by decide +kernel
theorem certified0230swap : Certified (graph core0230) (root 5) 3 2 :=
  of_native_maps core0230 DegreeOneSmallSpectrum1136.graph DegreeOneSmallSpectrum879.graph
    sourceMap0230swap fusedMap0230swap sourceMap0230swap_checked fusedMap0230swap_checked
    DegreeOneSmallComparisons.comparison0230
#print axioms sourceMap0230swap_checked
#print axioms fusedMap0230swap_checked
#print axioms certified0230swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
