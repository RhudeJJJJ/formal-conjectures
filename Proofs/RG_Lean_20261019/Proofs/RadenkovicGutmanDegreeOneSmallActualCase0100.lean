/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0100 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0100 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (sourceLabel 4 0 5 v)
def fusedMap0100 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10,11] (fusedLabel 4 0 5 v)
theorem sourceMap0100_checked : acceptsGraphIso
    (source (graph core0100) (root 4) 0 5) DegreeOneSmallSpectrum396.graph sourceMap0100=true := by decide +kernel
theorem fusedMap0100_checked : acceptsGraphIso
    (fused (graph core0100) (root 4) 0 5) DegreeOneSmallSpectrum369.graph fusedMap0100=true := by decide +kernel
theorem certified0100 : Certified (graph core0100) (root 4) 0 5 :=
  of_native_maps core0100 DegreeOneSmallSpectrum396.graph DegreeOneSmallSpectrum369.graph
    sourceMap0100 fusedMap0100 sourceMap0100_checked fusedMap0100_checked
    DegreeOneSmallComparisons.comparison0100
#print axioms sourceMap0100_checked
#print axioms fusedMap0100_checked
#print axioms certified0100
def sourceMap0100swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,7,8,9,10,11,6] (sourceLabel 4 5 0 v)
def fusedMap0100swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10,11] (fusedLabel 4 5 0 v)
theorem sourceMap0100swap_checked : acceptsGraphIso
    (source (graph core0100) (root 4) 5 0) DegreeOneSmallSpectrum396.graph sourceMap0100swap=true := by decide +kernel
theorem fusedMap0100swap_checked : acceptsGraphIso
    (fused (graph core0100) (root 4) 5 0) DegreeOneSmallSpectrum369.graph fusedMap0100swap=true := by decide +kernel
theorem certified0100swap : Certified (graph core0100) (root 4) 5 0 :=
  of_native_maps core0100 DegreeOneSmallSpectrum396.graph DegreeOneSmallSpectrum369.graph
    sourceMap0100swap fusedMap0100swap sourceMap0100swap_checked fusedMap0100swap_checked
    DegreeOneSmallComparisons.comparison0100
#print axioms sourceMap0100swap_checked
#print axioms fusedMap0100swap_checked
#print axioms certified0100swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
