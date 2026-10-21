/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0973 : Family 8 := level8.get ⟨84,by decide⟩
def sourceMap0973 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 8 0 2 v)
def fusedMap0973 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0973_checked : acceptsGraphIso
    (source (graph core0973) (root 8) 0 2) DegreeOneSmallSpectrum1505.graph sourceMap0973=true := by decide +kernel
theorem fusedMap0973_checked : acceptsGraphIso
    (fused (graph core0973) (root 8) 0 2) DegreeOneSmallSpectrum968.graph fusedMap0973=true := by decide +kernel
theorem certified0973 : Certified (graph core0973) (root 8) 0 2 :=
  of_native_maps core0973 DegreeOneSmallSpectrum1505.graph DegreeOneSmallSpectrum968.graph
    sourceMap0973 fusedMap0973 sourceMap0973_checked fusedMap0973_checked
    DegreeOneSmallComparisons.comparison0973
#print axioms sourceMap0973_checked
#print axioms fusedMap0973_checked
#print axioms certified0973
def sourceMap0973swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 2 0 v)
def fusedMap0973swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0973swap_checked : acceptsGraphIso
    (source (graph core0973) (root 8) 2 0) DegreeOneSmallSpectrum1505.graph sourceMap0973swap=true := by decide +kernel
theorem fusedMap0973swap_checked : acceptsGraphIso
    (fused (graph core0973) (root 8) 2 0) DegreeOneSmallSpectrum968.graph fusedMap0973swap=true := by decide +kernel
theorem certified0973swap : Certified (graph core0973) (root 8) 2 0 :=
  of_native_maps core0973 DegreeOneSmallSpectrum1505.graph DegreeOneSmallSpectrum968.graph
    sourceMap0973swap fusedMap0973swap sourceMap0973swap_checked fusedMap0973swap_checked
    DegreeOneSmallComparisons.comparison0973
#print axioms sourceMap0973swap_checked
#print axioms fusedMap0973swap_checked
#print axioms certified0973swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
