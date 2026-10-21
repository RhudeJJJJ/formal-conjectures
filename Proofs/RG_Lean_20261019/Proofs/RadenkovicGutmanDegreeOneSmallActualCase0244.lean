/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0244 : Family 5 := level5.get ⟨9,by decide⟩
def sourceMap0244 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,8,6,7] (sourceLabel 5 0 1 v)
def fusedMap0244 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 0 1 v)
theorem sourceMap0244_checked : acceptsGraphIso
    (source (graph core0244) (root 5) 0 1) DegreeOneSmallSpectrum057.graph sourceMap0244=true := by decide +kernel
theorem fusedMap0244_checked : acceptsGraphIso
    (fused (graph core0244) (root 5) 0 1) DegreeOneSmallSpectrum058.graph fusedMap0244=true := by decide +kernel
theorem certified0244 : Certified (graph core0244) (root 5) 0 1 :=
  of_native_maps core0244 DegreeOneSmallSpectrum057.graph DegreeOneSmallSpectrum058.graph
    sourceMap0244 fusedMap0244 sourceMap0244_checked fusedMap0244_checked
    DegreeOneSmallComparisons.comparison0244
#print axioms sourceMap0244_checked
#print axioms fusedMap0244_checked
#print axioms certified0244
def sourceMap0244swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,6,7,8] (sourceLabel 5 1 0 v)
def fusedMap0244swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 1 0 v)
theorem sourceMap0244swap_checked : acceptsGraphIso
    (source (graph core0244) (root 5) 1 0) DegreeOneSmallSpectrum057.graph sourceMap0244swap=true := by decide +kernel
theorem fusedMap0244swap_checked : acceptsGraphIso
    (fused (graph core0244) (root 5) 1 0) DegreeOneSmallSpectrum058.graph fusedMap0244swap=true := by decide +kernel
theorem certified0244swap : Certified (graph core0244) (root 5) 1 0 :=
  of_native_maps core0244 DegreeOneSmallSpectrum057.graph DegreeOneSmallSpectrum058.graph
    sourceMap0244swap fusedMap0244swap sourceMap0244swap_checked fusedMap0244swap_checked
    DegreeOneSmallComparisons.comparison0244
#print axioms sourceMap0244swap_checked
#print axioms fusedMap0244swap_checked
#print axioms certified0244swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
