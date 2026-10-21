/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0157 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0157 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,5,6,7,8,2,3,4,0,9,10,11,12] (sourceLabel 4 2 4 v)
def fusedMap0157 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 2 4 v)
theorem sourceMap0157_checked : acceptsGraphIso
    (source (graph core0157) (root 4) 2 4) DegreeOneSmallSpectrum1467.graph sourceMap0157=true := by decide +kernel
theorem fusedMap0157_checked : acceptsGraphIso
    (fused (graph core0157) (root 4) 2 4) DegreeOneSmallSpectrum870.graph fusedMap0157=true := by decide +kernel
theorem certified0157 : Certified (graph core0157) (root 4) 2 4 :=
  of_native_maps core0157 DegreeOneSmallSpectrum1467.graph DegreeOneSmallSpectrum870.graph
    sourceMap0157 fusedMap0157 sourceMap0157_checked fusedMap0157_checked
    DegreeOneSmallComparisons.comparison0157
#print axioms sourceMap0157_checked
#print axioms fusedMap0157_checked
#print axioms certified0157
def sourceMap0157swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,5,6,7,8,0,9,10,11,12,2,3,4] (sourceLabel 4 4 2 v)
def fusedMap0157swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 4 2 v)
theorem sourceMap0157swap_checked : acceptsGraphIso
    (source (graph core0157) (root 4) 4 2) DegreeOneSmallSpectrum1467.graph sourceMap0157swap=true := by decide +kernel
theorem fusedMap0157swap_checked : acceptsGraphIso
    (fused (graph core0157) (root 4) 4 2) DegreeOneSmallSpectrum870.graph fusedMap0157swap=true := by decide +kernel
theorem certified0157swap : Certified (graph core0157) (root 4) 4 2 :=
  of_native_maps core0157 DegreeOneSmallSpectrum1467.graph DegreeOneSmallSpectrum870.graph
    sourceMap0157swap fusedMap0157swap sourceMap0157swap_checked fusedMap0157swap_checked
    DegreeOneSmallComparisons.comparison0157
#print axioms sourceMap0157swap_checked
#print axioms fusedMap0157swap_checked
#print axioms certified0157swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
