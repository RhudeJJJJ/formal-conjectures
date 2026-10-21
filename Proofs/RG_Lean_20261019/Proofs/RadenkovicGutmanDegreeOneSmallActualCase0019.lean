/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0019 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0019 : (Vertices 1 ⊕ Fin 3 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,4,1,2,3,5,6,7,8] (sourceLabel 1 2 3 v)
def fusedMap0019 : (Vertices 1 ⊕ Fin 7) → Fin 9 :=
  fun v => ![3,4,2,1,0,5,6,7,8] (fusedLabel 1 2 3 v)
theorem sourceMap0019_checked : acceptsGraphIso
    (source (graph core0019) (root 1) 2 3) DegreeOneSmallSpectrum036.graph sourceMap0019=true := by decide +kernel
theorem fusedMap0019_checked : acceptsGraphIso
    (fused (graph core0019) (root 1) 2 3) DegreeOneSmallSpectrum037.graph fusedMap0019=true := by decide +kernel
theorem certified0019 : Certified (graph core0019) (root 1) 2 3 :=
  of_native_maps core0019 DegreeOneSmallSpectrum036.graph DegreeOneSmallSpectrum037.graph
    sourceMap0019 fusedMap0019 sourceMap0019_checked fusedMap0019_checked
    DegreeOneSmallComparisons.comparison0019
#print axioms sourceMap0019_checked
#print axioms fusedMap0019_checked
#print axioms certified0019
def sourceMap0019swap : (Vertices 1 ⊕ Fin 4 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,4,5,6,7,8,1,2,3] (sourceLabel 1 3 2 v)
def fusedMap0019swap : (Vertices 1 ⊕ Fin 7) → Fin 9 :=
  fun v => ![3,4,2,1,0,5,6,7,8] (fusedLabel 1 3 2 v)
theorem sourceMap0019swap_checked : acceptsGraphIso
    (source (graph core0019) (root 1) 3 2) DegreeOneSmallSpectrum036.graph sourceMap0019swap=true := by decide +kernel
theorem fusedMap0019swap_checked : acceptsGraphIso
    (fused (graph core0019) (root 1) 3 2) DegreeOneSmallSpectrum037.graph fusedMap0019swap=true := by decide +kernel
theorem certified0019swap : Certified (graph core0019) (root 1) 3 2 :=
  of_native_maps core0019 DegreeOneSmallSpectrum036.graph DegreeOneSmallSpectrum037.graph
    sourceMap0019swap fusedMap0019swap sourceMap0019swap_checked fusedMap0019swap_checked
    DegreeOneSmallComparisons.comparison0019
#print axioms sourceMap0019swap_checked
#print axioms fusedMap0019swap_checked
#print axioms certified0019swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
