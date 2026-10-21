/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0079 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0079 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (sourceLabel 3 0 4 v)
def fusedMap0079 : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (fusedLabel 3 0 4 v)
theorem sourceMap0079_checked : acceptsGraphIso
    (source (graph core0079) (root 3) 0 4) DegreeOneSmallSpectrum075.graph sourceMap0079=true := by decide +kernel
theorem fusedMap0079_checked : acceptsGraphIso
    (fused (graph core0079) (root 3) 0 4) DegreeOneSmallSpectrum080.graph fusedMap0079=true := by decide +kernel
theorem certified0079 : Certified (graph core0079) (root 3) 0 4 :=
  of_native_maps core0079 DegreeOneSmallSpectrum075.graph DegreeOneSmallSpectrum080.graph
    sourceMap0079 fusedMap0079 sourceMap0079_checked fusedMap0079_checked
    DegreeOneSmallComparisons.comparison0079
#print axioms sourceMap0079_checked
#print axioms fusedMap0079_checked
#print axioms certified0079
def sourceMap0079swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,2,3,4,0,6,7,8,9,5] (sourceLabel 3 4 0 v)
def fusedMap0079swap : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (fusedLabel 3 4 0 v)
theorem sourceMap0079swap_checked : acceptsGraphIso
    (source (graph core0079) (root 3) 4 0) DegreeOneSmallSpectrum075.graph sourceMap0079swap=true := by decide +kernel
theorem fusedMap0079swap_checked : acceptsGraphIso
    (fused (graph core0079) (root 3) 4 0) DegreeOneSmallSpectrum080.graph fusedMap0079swap=true := by decide +kernel
theorem certified0079swap : Certified (graph core0079) (root 3) 4 0 :=
  of_native_maps core0079 DegreeOneSmallSpectrum075.graph DegreeOneSmallSpectrum080.graph
    sourceMap0079swap fusedMap0079swap sourceMap0079swap_checked fusedMap0079swap_checked
    DegreeOneSmallComparisons.comparison0079
#print axioms sourceMap0079swap_checked
#print axioms fusedMap0079swap_checked
#print axioms certified0079swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
