/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0096 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0096 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 2) → Fin 8 :=
  fun v => ![1,0,5,6,7,4,2,3] (sourceLabel 4 0 1 v)
def fusedMap0096 : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,4,5,6,7,1,2,3] (fusedLabel 4 0 1 v)
theorem sourceMap0096_checked : acceptsGraphIso
    (source (graph core0096) (root 4) 0 1) DegreeOneSmallSpectrum025.graph sourceMap0096=true := by decide +kernel
theorem fusedMap0096_checked : acceptsGraphIso
    (fused (graph core0096) (root 4) 0 1) DegreeOneSmallSpectrum016.graph fusedMap0096=true := by decide +kernel
theorem certified0096 : Certified (graph core0096) (root 4) 0 1 :=
  of_native_maps core0096 DegreeOneSmallSpectrum025.graph DegreeOneSmallSpectrum016.graph
    sourceMap0096 fusedMap0096 sourceMap0096_checked fusedMap0096_checked
    DegreeOneSmallComparisons.comparison0096
#print axioms sourceMap0096_checked
#print axioms fusedMap0096_checked
#print axioms certified0096
def sourceMap0096swap : (Vertices 4 ⊕ Fin 2 ⊕ Fin 1) → Fin 8 :=
  fun v => ![1,0,5,6,7,2,3,4] (sourceLabel 4 1 0 v)
def fusedMap0096swap : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,4,5,6,7,1,2,3] (fusedLabel 4 1 0 v)
theorem sourceMap0096swap_checked : acceptsGraphIso
    (source (graph core0096) (root 4) 1 0) DegreeOneSmallSpectrum025.graph sourceMap0096swap=true := by decide +kernel
theorem fusedMap0096swap_checked : acceptsGraphIso
    (fused (graph core0096) (root 4) 1 0) DegreeOneSmallSpectrum016.graph fusedMap0096swap=true := by decide +kernel
theorem certified0096swap : Certified (graph core0096) (root 4) 1 0 :=
  of_native_maps core0096 DegreeOneSmallSpectrum025.graph DegreeOneSmallSpectrum016.graph
    sourceMap0096swap fusedMap0096swap sourceMap0096swap_checked fusedMap0096swap_checked
    DegreeOneSmallComparisons.comparison0096
#print axioms sourceMap0096swap_checked
#print axioms fusedMap0096swap_checked
#print axioms certified0096swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
