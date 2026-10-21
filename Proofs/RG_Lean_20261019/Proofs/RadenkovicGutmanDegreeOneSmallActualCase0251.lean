/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0251 : Family 5 := level5.get ⟨9,by decide⟩
def sourceMap0251 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 1 3 v)
def fusedMap0251 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 1 3 v)
theorem sourceMap0251_checked : acceptsGraphIso
    (source (graph core0251) (root 5) 1 3) DegreeOneSmallSpectrum524.graph sourceMap0251=true := by decide +kernel
theorem fusedMap0251_checked : acceptsGraphIso
    (fused (graph core0251) (root 5) 1 3) DegreeOneSmallSpectrum380.graph fusedMap0251=true := by decide +kernel
theorem certified0251 : Certified (graph core0251) (root 5) 1 3 :=
  of_native_maps core0251 DegreeOneSmallSpectrum524.graph DegreeOneSmallSpectrum380.graph
    sourceMap0251 fusedMap0251 sourceMap0251_checked fusedMap0251_checked
    DegreeOneSmallComparisons.comparison0251
#print axioms sourceMap0251_checked
#print axioms fusedMap0251_checked
#print axioms certified0251
def sourceMap0251swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,6,7] (sourceLabel 5 3 1 v)
def fusedMap0251swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 3 1 v)
theorem sourceMap0251swap_checked : acceptsGraphIso
    (source (graph core0251) (root 5) 3 1) DegreeOneSmallSpectrum524.graph sourceMap0251swap=true := by decide +kernel
theorem fusedMap0251swap_checked : acceptsGraphIso
    (fused (graph core0251) (root 5) 3 1) DegreeOneSmallSpectrum380.graph fusedMap0251swap=true := by decide +kernel
theorem certified0251swap : Certified (graph core0251) (root 5) 3 1 :=
  of_native_maps core0251 DegreeOneSmallSpectrum524.graph DegreeOneSmallSpectrum380.graph
    sourceMap0251swap fusedMap0251swap sourceMap0251swap_checked fusedMap0251swap_checked
    DegreeOneSmallComparisons.comparison0251
#print axioms sourceMap0251swap_checked
#print axioms fusedMap0251swap_checked
#print axioms certified0251swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
