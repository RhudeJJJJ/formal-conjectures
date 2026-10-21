/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0001 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0001 : (Vertices 1 ⊕ Fin 1 ⊕ Fin 2) → Fin 5 :=
  fun v => ![0,1,2,3,4] (sourceLabel 1 0 1 v)
def fusedMap0001 : (Vertices 1 ⊕ Fin 3) → Fin 5 :=
  fun v => ![1,2,0,3,4] (fusedLabel 1 0 1 v)
theorem sourceMap0001_checked : acceptsGraphIso
    (source (graph core0001) (root 1) 0 1) DegreeOneSmallSpectrum002.graph sourceMap0001=true := by decide +kernel
theorem fusedMap0001_checked : acceptsGraphIso
    (fused (graph core0001) (root 1) 0 1) DegreeOneSmallSpectrum003.graph fusedMap0001=true := by decide +kernel
theorem certified0001 : Certified (graph core0001) (root 1) 0 1 :=
  of_native_maps core0001 DegreeOneSmallSpectrum002.graph DegreeOneSmallSpectrum003.graph
    sourceMap0001 fusedMap0001 sourceMap0001_checked fusedMap0001_checked
    DegreeOneSmallComparisons.comparison0001
#print axioms sourceMap0001_checked
#print axioms fusedMap0001_checked
#print axioms certified0001
def sourceMap0001swap : (Vertices 1 ⊕ Fin 2 ⊕ Fin 1) → Fin 5 :=
  fun v => ![0,1,3,4,2] (sourceLabel 1 1 0 v)
def fusedMap0001swap : (Vertices 1 ⊕ Fin 3) → Fin 5 :=
  fun v => ![1,2,0,3,4] (fusedLabel 1 1 0 v)
theorem sourceMap0001swap_checked : acceptsGraphIso
    (source (graph core0001) (root 1) 1 0) DegreeOneSmallSpectrum002.graph sourceMap0001swap=true := by decide +kernel
theorem fusedMap0001swap_checked : acceptsGraphIso
    (fused (graph core0001) (root 1) 1 0) DegreeOneSmallSpectrum003.graph fusedMap0001swap=true := by decide +kernel
theorem certified0001swap : Certified (graph core0001) (root 1) 1 0 :=
  of_native_maps core0001 DegreeOneSmallSpectrum002.graph DegreeOneSmallSpectrum003.graph
    sourceMap0001swap fusedMap0001swap sourceMap0001swap_checked fusedMap0001swap_checked
    DegreeOneSmallComparisons.comparison0001
#print axioms sourceMap0001swap_checked
#print axioms fusedMap0001swap_checked
#print axioms certified0001swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
