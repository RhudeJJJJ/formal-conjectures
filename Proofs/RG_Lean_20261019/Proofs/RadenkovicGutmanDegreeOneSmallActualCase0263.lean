/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0263 : Family 5 := level5.get ⟨13,by decide⟩
def sourceMap0263 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (sourceLabel 5 1 3 v)
def fusedMap0263 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 1 3 v)
theorem sourceMap0263_checked : acceptsGraphIso
    (source (graph core0263) (root 5) 1 3) DegreeOneSmallSpectrum608.graph sourceMap0263=true := by decide +kernel
theorem fusedMap0263_checked : acceptsGraphIso
    (fused (graph core0263) (root 5) 1 3) SmallGeFourSpectrum094.graph fusedMap0263=true := by decide +kernel
theorem certified0263 : Certified (graph core0263) (root 5) 1 3 :=
  of_native_maps core0263 DegreeOneSmallSpectrum608.graph SmallGeFourSpectrum094.graph
    sourceMap0263 fusedMap0263 sourceMap0263_checked fusedMap0263_checked
    DegreeOneSmallComparisons.comparison0263
#print axioms sourceMap0263_checked
#print axioms fusedMap0263_checked
#print axioms certified0263
def sourceMap0263swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,9,10,11,7,8] (sourceLabel 5 3 1 v)
def fusedMap0263swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 3 1 v)
theorem sourceMap0263swap_checked : acceptsGraphIso
    (source (graph core0263) (root 5) 3 1) DegreeOneSmallSpectrum608.graph sourceMap0263swap=true := by decide +kernel
theorem fusedMap0263swap_checked : acceptsGraphIso
    (fused (graph core0263) (root 5) 3 1) SmallGeFourSpectrum094.graph fusedMap0263swap=true := by decide +kernel
theorem certified0263swap : Certified (graph core0263) (root 5) 3 1 :=
  of_native_maps core0263 DegreeOneSmallSpectrum608.graph SmallGeFourSpectrum094.graph
    sourceMap0263swap fusedMap0263swap sourceMap0263swap_checked fusedMap0263swap_checked
    DegreeOneSmallComparisons.comparison0263
#print axioms sourceMap0263swap_checked
#print axioms fusedMap0263swap_checked
#print axioms certified0263swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
