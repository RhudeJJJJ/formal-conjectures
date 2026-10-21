/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0636 : Family 7 := level7.get ⟨45,by decide⟩
def sourceMap0636 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0636 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0636_checked : acceptsGraphIso
    (source (graph core0636) (root 7) 0 3) DegreeOneSmallSpectrum1414.graph sourceMap0636=true := by decide +kernel
theorem fusedMap0636_checked : acceptsGraphIso
    (fused (graph core0636) (root 7) 0 3) DegreeOneSmallSpectrum923.graph fusedMap0636=true := by decide +kernel
theorem certified0636 : Certified (graph core0636) (root 7) 0 3 :=
  of_native_maps core0636 DegreeOneSmallSpectrum1414.graph DegreeOneSmallSpectrum923.graph
    sourceMap0636 fusedMap0636 sourceMap0636_checked fusedMap0636_checked
    DegreeOneSmallComparisons.comparison0636
#print axioms sourceMap0636_checked
#print axioms fusedMap0636_checked
#print axioms certified0636
def sourceMap0636swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0636swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0636swap_checked : acceptsGraphIso
    (source (graph core0636) (root 7) 3 0) DegreeOneSmallSpectrum1414.graph sourceMap0636swap=true := by decide +kernel
theorem fusedMap0636swap_checked : acceptsGraphIso
    (fused (graph core0636) (root 7) 3 0) DegreeOneSmallSpectrum923.graph fusedMap0636swap=true := by decide +kernel
theorem certified0636swap : Certified (graph core0636) (root 7) 3 0 :=
  of_native_maps core0636 DegreeOneSmallSpectrum1414.graph DegreeOneSmallSpectrum923.graph
    sourceMap0636swap fusedMap0636swap sourceMap0636swap_checked fusedMap0636swap_checked
    DegreeOneSmallComparisons.comparison0636
#print axioms sourceMap0636swap_checked
#print axioms fusedMap0636swap_checked
#print axioms certified0636swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
