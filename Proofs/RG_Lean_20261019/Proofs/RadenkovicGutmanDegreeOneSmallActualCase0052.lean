/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0052 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0052 : (Vertices 2 ⊕ Fin 4 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,5,6,1,2,3,4,7,8,9,10,11] (sourceLabel 2 3 4 v)
def fusedMap0052 : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10,11] (fusedLabel 2 3 4 v)
theorem sourceMap0052_checked : acceptsGraphIso
    (source (graph core0052) (root 2) 3 4) DegreeOneSmallSpectrum393.graph sourceMap0052=true := by decide +kernel
theorem fusedMap0052_checked : acceptsGraphIso
    (fused (graph core0052) (root 2) 3 4) DegreeOneSmallSpectrum369.graph fusedMap0052=true := by decide +kernel
theorem certified0052 : Certified (graph core0052) (root 2) 3 4 :=
  of_native_maps core0052 DegreeOneSmallSpectrum393.graph DegreeOneSmallSpectrum369.graph
    sourceMap0052 fusedMap0052 sourceMap0052_checked fusedMap0052_checked
    DegreeOneSmallComparisons.comparison0052
#print axioms sourceMap0052_checked
#print axioms fusedMap0052_checked
#print axioms certified0052
def sourceMap0052swap : (Vertices 2 ⊕ Fin 5 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,5,6,7,8,9,10,11,1,2,3,4] (sourceLabel 2 4 3 v)
def fusedMap0052swap : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10,11] (fusedLabel 2 4 3 v)
theorem sourceMap0052swap_checked : acceptsGraphIso
    (source (graph core0052) (root 2) 4 3) DegreeOneSmallSpectrum393.graph sourceMap0052swap=true := by decide +kernel
theorem fusedMap0052swap_checked : acceptsGraphIso
    (fused (graph core0052) (root 2) 4 3) DegreeOneSmallSpectrum369.graph fusedMap0052swap=true := by decide +kernel
theorem certified0052swap : Certified (graph core0052) (root 2) 4 3 :=
  of_native_maps core0052 DegreeOneSmallSpectrum393.graph DegreeOneSmallSpectrum369.graph
    sourceMap0052swap fusedMap0052swap sourceMap0052swap_checked fusedMap0052swap_checked
    DegreeOneSmallComparisons.comparison0052
#print axioms sourceMap0052swap_checked
#print axioms fusedMap0052swap_checked
#print axioms certified0052swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
