/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0976 : Family 8 := level8.get ⟨85,by decide⟩
def sourceMap0976 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0976 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (fusedLabel 8 0 1 v)
theorem sourceMap0976_checked : acceptsGraphIso
    (source (graph core0976) (root 8) 0 1) DegreeOneSmallSpectrum537.graph sourceMap0976=true := by decide +kernel
theorem fusedMap0976_checked : acceptsGraphIso
    (fused (graph core0976) (root 8) 0 1) DegreeOneSmallSpectrum587.graph fusedMap0976=true := by decide +kernel
theorem certified0976 : Certified (graph core0976) (root 8) 0 1 :=
  of_native_maps core0976 DegreeOneSmallSpectrum537.graph DegreeOneSmallSpectrum587.graph
    sourceMap0976 fusedMap0976 sourceMap0976_checked fusedMap0976_checked
    DegreeOneSmallComparisons.comparison0976
#print axioms sourceMap0976_checked
#print axioms fusedMap0976_checked
#print axioms certified0976
def sourceMap0976swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0976swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (fusedLabel 8 1 0 v)
theorem sourceMap0976swap_checked : acceptsGraphIso
    (source (graph core0976) (root 8) 1 0) DegreeOneSmallSpectrum537.graph sourceMap0976swap=true := by decide +kernel
theorem fusedMap0976swap_checked : acceptsGraphIso
    (fused (graph core0976) (root 8) 1 0) DegreeOneSmallSpectrum587.graph fusedMap0976swap=true := by decide +kernel
theorem certified0976swap : Certified (graph core0976) (root 8) 1 0 :=
  of_native_maps core0976 DegreeOneSmallSpectrum537.graph DegreeOneSmallSpectrum587.graph
    sourceMap0976swap fusedMap0976swap sourceMap0976swap_checked fusedMap0976swap_checked
    DegreeOneSmallComparisons.comparison0976
#print axioms sourceMap0976swap_checked
#print axioms fusedMap0976swap_checked
#print axioms certified0976swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
