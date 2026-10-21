/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0390 : Family 6 := level6.get ⟨19,by decide⟩
def sourceMap0390 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0390 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0390_checked : acceptsGraphIso
    (source (graph core0390) (root 6) 1 2) DegreeOneSmallSpectrum624.graph sourceMap0390=true := by decide +kernel
theorem fusedMap0390_checked : acceptsGraphIso
    (fused (graph core0390) (root 6) 1 2) SmallGeFourSpectrum094.graph fusedMap0390=true := by decide +kernel
theorem certified0390 : Certified (graph core0390) (root 6) 1 2 :=
  of_native_maps core0390 DegreeOneSmallSpectrum624.graph SmallGeFourSpectrum094.graph
    sourceMap0390 fusedMap0390 sourceMap0390_checked fusedMap0390_checked
    DegreeOneSmallComparisons.comparison0390
#print axioms sourceMap0390_checked
#print axioms fusedMap0390_checked
#print axioms certified0390
def sourceMap0390swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0390swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0390swap_checked : acceptsGraphIso
    (source (graph core0390) (root 6) 2 1) DegreeOneSmallSpectrum624.graph sourceMap0390swap=true := by decide +kernel
theorem fusedMap0390swap_checked : acceptsGraphIso
    (fused (graph core0390) (root 6) 2 1) SmallGeFourSpectrum094.graph fusedMap0390swap=true := by decide +kernel
theorem certified0390swap : Certified (graph core0390) (root 6) 2 1 :=
  of_native_maps core0390 DegreeOneSmallSpectrum624.graph SmallGeFourSpectrum094.graph
    sourceMap0390swap fusedMap0390swap sourceMap0390swap_checked fusedMap0390swap_checked
    DegreeOneSmallComparisons.comparison0390
#print axioms sourceMap0390swap_checked
#print axioms fusedMap0390swap_checked
#print axioms certified0390swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
