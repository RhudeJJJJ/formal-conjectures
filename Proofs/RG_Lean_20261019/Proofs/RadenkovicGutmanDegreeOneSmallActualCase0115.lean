/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0115 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0115 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (sourceLabel 4 0 4 v)
def fusedMap0115 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 0 4 v)
theorem sourceMap0115_checked : acceptsGraphIso
    (source (graph core0115) (root 4) 0 4) DegreeOneSmallSpectrum188.graph sourceMap0115=true := by decide +kernel
theorem fusedMap0115_checked : acceptsGraphIso
    (fused (graph core0115) (root 4) 0 4) DegreeOneSmallSpectrum164.graph fusedMap0115=true := by decide +kernel
theorem certified0115 : Certified (graph core0115) (root 4) 0 4 :=
  of_native_maps core0115 DegreeOneSmallSpectrum188.graph DegreeOneSmallSpectrum164.graph
    sourceMap0115 fusedMap0115 sourceMap0115_checked fusedMap0115_checked
    DegreeOneSmallComparisons.comparison0115
#print axioms sourceMap0115_checked
#print axioms fusedMap0115_checked
#print axioms certified0115
def sourceMap0115swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,7,8,9,10,6] (sourceLabel 4 4 0 v)
def fusedMap0115swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,6,7,8,9,10] (fusedLabel 4 4 0 v)
theorem sourceMap0115swap_checked : acceptsGraphIso
    (source (graph core0115) (root 4) 4 0) DegreeOneSmallSpectrum188.graph sourceMap0115swap=true := by decide +kernel
theorem fusedMap0115swap_checked : acceptsGraphIso
    (fused (graph core0115) (root 4) 4 0) DegreeOneSmallSpectrum164.graph fusedMap0115swap=true := by decide +kernel
theorem certified0115swap : Certified (graph core0115) (root 4) 4 0 :=
  of_native_maps core0115 DegreeOneSmallSpectrum188.graph DegreeOneSmallSpectrum164.graph
    sourceMap0115swap fusedMap0115swap sourceMap0115swap_checked fusedMap0115swap_checked
    DegreeOneSmallComparisons.comparison0115
#print axioms sourceMap0115swap_checked
#print axioms fusedMap0115swap_checked
#print axioms certified0115swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
