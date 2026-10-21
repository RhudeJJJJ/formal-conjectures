/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0078 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0078 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (sourceLabel 3 0 3 v)
def fusedMap0078 : (Vertices 3 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,2,3,4,0,5,6,7,8] (fusedLabel 3 0 3 v)
theorem sourceMap0078_checked : acceptsGraphIso
    (source (graph core0078) (root 3) 0 3) DegreeOneSmallSpectrum047.graph sourceMap0078=true := by decide +kernel
theorem fusedMap0078_checked : acceptsGraphIso
    (fused (graph core0078) (root 3) 0 3) DegreeOneSmallSpectrum034.graph fusedMap0078=true := by decide +kernel
theorem certified0078 : Certified (graph core0078) (root 3) 0 3 :=
  of_native_maps core0078 DegreeOneSmallSpectrum047.graph DegreeOneSmallSpectrum034.graph
    sourceMap0078 fusedMap0078 sourceMap0078_checked fusedMap0078_checked
    DegreeOneSmallComparisons.comparison0078
#print axioms sourceMap0078_checked
#print axioms fusedMap0078_checked
#print axioms certified0078
def sourceMap0078swap : (Vertices 3 ⊕ Fin 4 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,2,3,4,0,6,7,8,5] (sourceLabel 3 3 0 v)
def fusedMap0078swap : (Vertices 3 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,2,3,4,0,5,6,7,8] (fusedLabel 3 3 0 v)
theorem sourceMap0078swap_checked : acceptsGraphIso
    (source (graph core0078) (root 3) 3 0) DegreeOneSmallSpectrum047.graph sourceMap0078swap=true := by decide +kernel
theorem fusedMap0078swap_checked : acceptsGraphIso
    (fused (graph core0078) (root 3) 3 0) DegreeOneSmallSpectrum034.graph fusedMap0078swap=true := by decide +kernel
theorem certified0078swap : Certified (graph core0078) (root 3) 3 0 :=
  of_native_maps core0078 DegreeOneSmallSpectrum047.graph DegreeOneSmallSpectrum034.graph
    sourceMap0078swap fusedMap0078swap sourceMap0078swap_checked fusedMap0078swap_checked
    DegreeOneSmallComparisons.comparison0078
#print axioms sourceMap0078swap_checked
#print axioms fusedMap0078swap_checked
#print axioms certified0078swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
