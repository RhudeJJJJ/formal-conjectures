/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0064 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0064 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,7,8,4,5,6] (sourceLabel 3 1 2 v)
def fusedMap0064 : (Vertices 3 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,2,3,4,0,5,6,7,8] (fusedLabel 3 1 2 v)
theorem sourceMap0064_checked : acceptsGraphIso
    (source (graph core0064) (root 3) 1 2) DegreeOneSmallSpectrum061.graph sourceMap0064=true := by decide +kernel
theorem fusedMap0064_checked : acceptsGraphIso
    (fused (graph core0064) (root 3) 1 2) DegreeOneSmallSpectrum037.graph fusedMap0064=true := by decide +kernel
theorem certified0064 : Certified (graph core0064) (root 3) 1 2 :=
  of_native_maps core0064 DegreeOneSmallSpectrum061.graph DegreeOneSmallSpectrum037.graph
    sourceMap0064 fusedMap0064 sourceMap0064_checked fusedMap0064_checked
    DegreeOneSmallComparisons.comparison0064
#print axioms sourceMap0064_checked
#print axioms fusedMap0064_checked
#print axioms certified0064
def sourceMap0064swap : (Vertices 3 ⊕ Fin 3 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 3 2 1 v)
def fusedMap0064swap : (Vertices 3 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,2,3,4,0,5,6,7,8] (fusedLabel 3 2 1 v)
theorem sourceMap0064swap_checked : acceptsGraphIso
    (source (graph core0064) (root 3) 2 1) DegreeOneSmallSpectrum061.graph sourceMap0064swap=true := by decide +kernel
theorem fusedMap0064swap_checked : acceptsGraphIso
    (fused (graph core0064) (root 3) 2 1) DegreeOneSmallSpectrum037.graph fusedMap0064swap=true := by decide +kernel
theorem certified0064swap : Certified (graph core0064) (root 3) 2 1 :=
  of_native_maps core0064 DegreeOneSmallSpectrum061.graph DegreeOneSmallSpectrum037.graph
    sourceMap0064swap fusedMap0064swap sourceMap0064swap_checked fusedMap0064swap_checked
    DegreeOneSmallComparisons.comparison0064
#print axioms sourceMap0064swap_checked
#print axioms fusedMap0064swap_checked
#print axioms certified0064swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
