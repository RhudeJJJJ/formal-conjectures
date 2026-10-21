/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0119 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0119 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,8,9,5,6,7] (sourceLabel 4 1 2 v)
def fusedMap0119 : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 1 2 v)
theorem sourceMap0119_checked : acceptsGraphIso
    (source (graph core0119) (root 4) 1 2) DegreeOneSmallSpectrum128.graph sourceMap0119=true := by decide +kernel
theorem fusedMap0119_checked : acceptsGraphIso
    (fused (graph core0119) (root 4) 1 2) DegreeOneSmallSpectrum080.graph fusedMap0119=true := by decide +kernel
theorem certified0119 : Certified (graph core0119) (root 4) 1 2 :=
  of_native_maps core0119 DegreeOneSmallSpectrum128.graph DegreeOneSmallSpectrum080.graph
    sourceMap0119 fusedMap0119 sourceMap0119_checked fusedMap0119_checked
    DegreeOneSmallComparisons.comparison0119
#print axioms sourceMap0119_checked
#print axioms fusedMap0119_checked
#print axioms certified0119
def sourceMap0119swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 4 2 1 v)
def fusedMap0119swap : (Vertices 4 ⊕ Fin 5) → Fin 10 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9] (fusedLabel 4 2 1 v)
theorem sourceMap0119swap_checked : acceptsGraphIso
    (source (graph core0119) (root 4) 2 1) DegreeOneSmallSpectrum128.graph sourceMap0119swap=true := by decide +kernel
theorem fusedMap0119swap_checked : acceptsGraphIso
    (fused (graph core0119) (root 4) 2 1) DegreeOneSmallSpectrum080.graph fusedMap0119swap=true := by decide +kernel
theorem certified0119swap : Certified (graph core0119) (root 4) 2 1 :=
  of_native_maps core0119 DegreeOneSmallSpectrum128.graph DegreeOneSmallSpectrum080.graph
    sourceMap0119swap fusedMap0119swap sourceMap0119swap_checked fusedMap0119swap_checked
    DegreeOneSmallComparisons.comparison0119
#print axioms sourceMap0119swap_checked
#print axioms fusedMap0119swap_checked
#print axioms certified0119swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
