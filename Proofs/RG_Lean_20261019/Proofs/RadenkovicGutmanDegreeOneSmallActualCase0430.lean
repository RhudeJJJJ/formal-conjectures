/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0430 : Family 6 := level6.get ⟨29,by decide⟩
def sourceMap0430 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (sourceLabel 6 0 1 v)
def fusedMap0430 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0430_checked : acceptsGraphIso
    (source (graph core0430) (root 6) 0 1) SmallGeFourSpectrum021.graph sourceMap0430=true := by decide +kernel
theorem fusedMap0430_checked : acceptsGraphIso
    (fused (graph core0430) (root 6) 0 1) SmallGeFourSpectrum022.graph fusedMap0430=true := by decide +kernel
theorem certified0430 : Certified (graph core0430) (root 6) 0 1 :=
  of_native_maps core0430 SmallGeFourSpectrum021.graph SmallGeFourSpectrum022.graph
    sourceMap0430 fusedMap0430 sourceMap0430_checked fusedMap0430_checked
    DegreeOneSmallComparisons.comparison0430
#print axioms sourceMap0430_checked
#print axioms fusedMap0430_checked
#print axioms certified0430
def sourceMap0430swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (sourceLabel 6 1 0 v)
def fusedMap0430swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0430swap_checked : acceptsGraphIso
    (source (graph core0430) (root 6) 1 0) SmallGeFourSpectrum021.graph sourceMap0430swap=true := by decide +kernel
theorem fusedMap0430swap_checked : acceptsGraphIso
    (fused (graph core0430) (root 6) 1 0) SmallGeFourSpectrum022.graph fusedMap0430swap=true := by decide +kernel
theorem certified0430swap : Certified (graph core0430) (root 6) 1 0 :=
  of_native_maps core0430 SmallGeFourSpectrum021.graph SmallGeFourSpectrum022.graph
    sourceMap0430swap fusedMap0430swap sourceMap0430swap_checked fusedMap0430swap_checked
    DegreeOneSmallComparisons.comparison0430
#print axioms sourceMap0430swap_checked
#print axioms fusedMap0430swap_checked
#print axioms certified0430swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
