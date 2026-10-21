/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0957 : Family 8 := level8.get ⟨76,by decide⟩
def sourceMap0957 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,11,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap0957 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0957_checked : acceptsGraphIso
    (source (graph core0957) (root 8) 0 2) DegreeOneSmallSpectrum1499.graph sourceMap0957=true := by decide +kernel
theorem fusedMap0957_checked : acceptsGraphIso
    (fused (graph core0957) (root 8) 0 2) DegreeOneSmallSpectrum953.graph fusedMap0957=true := by decide +kernel
theorem certified0957 : Certified (graph core0957) (root 8) 0 2 :=
  of_native_maps core0957 DegreeOneSmallSpectrum1499.graph DegreeOneSmallSpectrum953.graph
    sourceMap0957 fusedMap0957 sourceMap0957_checked fusedMap0957_checked
    DegreeOneSmallComparisons.comparison0957
#print axioms sourceMap0957_checked
#print axioms fusedMap0957_checked
#print axioms certified0957
def sourceMap0957swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 8 2 0 v)
def fusedMap0957swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0957swap_checked : acceptsGraphIso
    (source (graph core0957) (root 8) 2 0) DegreeOneSmallSpectrum1499.graph sourceMap0957swap=true := by decide +kernel
theorem fusedMap0957swap_checked : acceptsGraphIso
    (fused (graph core0957) (root 8) 2 0) DegreeOneSmallSpectrum953.graph fusedMap0957swap=true := by decide +kernel
theorem certified0957swap : Certified (graph core0957) (root 8) 2 0 :=
  of_native_maps core0957 DegreeOneSmallSpectrum1499.graph DegreeOneSmallSpectrum953.graph
    sourceMap0957swap fusedMap0957swap sourceMap0957swap_checked fusedMap0957swap_checked
    DegreeOneSmallComparisons.comparison0957
#print axioms sourceMap0957swap_checked
#print axioms fusedMap0957swap_checked
#print axioms certified0957swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
