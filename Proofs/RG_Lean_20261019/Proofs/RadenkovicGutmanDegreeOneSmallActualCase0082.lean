/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0082 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0082 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (sourceLabel 3 0 7 v)
def fusedMap0082 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 0 7 v)
theorem sourceMap0082_checked : acceptsGraphIso
    (source (graph core0082) (root 3) 0 7) DegreeOneSmallSpectrum879.graph sourceMap0082=true := by decide +kernel
theorem fusedMap0082_checked : acceptsGraphIso
    (fused (graph core0082) (root 3) 0 7) DegreeOneSmallSpectrum856.graph fusedMap0082=true := by decide +kernel
theorem certified0082 : Certified (graph core0082) (root 3) 0 7 :=
  of_native_maps core0082 DegreeOneSmallSpectrum879.graph DegreeOneSmallSpectrum856.graph
    sourceMap0082 fusedMap0082 sourceMap0082_checked fusedMap0082_checked
    DegreeOneSmallComparisons.comparison0082
#print axioms sourceMap0082_checked
#print axioms fusedMap0082_checked
#print axioms certified0082
def sourceMap0082swap : (Vertices 3 ⊕ Fin 8 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,8,9,10,11,12,7] (sourceLabel 3 7 0 v)
def fusedMap0082swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 7 0 v)
theorem sourceMap0082swap_checked : acceptsGraphIso
    (source (graph core0082) (root 3) 7 0) DegreeOneSmallSpectrum879.graph sourceMap0082swap=true := by decide +kernel
theorem fusedMap0082swap_checked : acceptsGraphIso
    (fused (graph core0082) (root 3) 7 0) DegreeOneSmallSpectrum856.graph fusedMap0082swap=true := by decide +kernel
theorem certified0082swap : Certified (graph core0082) (root 3) 7 0 :=
  of_native_maps core0082 DegreeOneSmallSpectrum879.graph DegreeOneSmallSpectrum856.graph
    sourceMap0082swap fusedMap0082swap sourceMap0082swap_checked fusedMap0082swap_checked
    DegreeOneSmallComparisons.comparison0082
#print axioms sourceMap0082swap_checked
#print axioms fusedMap0082swap_checked
#print axioms certified0082swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
