/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0440 : Family 6 := level6.get ⟨37,by decide⟩
def sourceMap0440 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 0 2 v)
def fusedMap0440 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0440_checked : acceptsGraphIso
    (source (graph core0440) (root 6) 0 2) SmallGeFourSpectrum041.graph sourceMap0440=true := by decide +kernel
theorem fusedMap0440_checked : acceptsGraphIso
    (fused (graph core0440) (root 6) 0 2) SmallGeFourSpectrum044.graph fusedMap0440=true := by decide +kernel
theorem certified0440 : Certified (graph core0440) (root 6) 0 2 :=
  of_native_maps core0440 SmallGeFourSpectrum041.graph SmallGeFourSpectrum044.graph
    sourceMap0440 fusedMap0440 sourceMap0440_checked fusedMap0440_checked
    DegreeOneSmallComparisons.comparison0440
#print axioms sourceMap0440_checked
#print axioms fusedMap0440_checked
#print axioms certified0440
def sourceMap0440swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,7] (sourceLabel 6 2 0 v)
def fusedMap0440swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0440swap_checked : acceptsGraphIso
    (source (graph core0440) (root 6) 2 0) SmallGeFourSpectrum041.graph sourceMap0440swap=true := by decide +kernel
theorem fusedMap0440swap_checked : acceptsGraphIso
    (fused (graph core0440) (root 6) 2 0) SmallGeFourSpectrum044.graph fusedMap0440swap=true := by decide +kernel
theorem certified0440swap : Certified (graph core0440) (root 6) 2 0 :=
  of_native_maps core0440 SmallGeFourSpectrum041.graph SmallGeFourSpectrum044.graph
    sourceMap0440swap fusedMap0440swap sourceMap0440swap_checked fusedMap0440swap_checked
    DegreeOneSmallComparisons.comparison0440
#print axioms sourceMap0440swap_checked
#print axioms fusedMap0440swap_checked
#print axioms certified0440swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
