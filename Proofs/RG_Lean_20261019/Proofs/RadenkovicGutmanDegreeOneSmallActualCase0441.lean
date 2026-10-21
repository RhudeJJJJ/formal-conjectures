/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0441 : Family 6 := level6.get ⟨37,by decide⟩
def sourceMap0441 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (sourceLabel 6 0 3 v)
def fusedMap0441 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0441_checked : acceptsGraphIso
    (source (graph core0441) (root 6) 0 3) SmallGeFourSpectrum121.graph sourceMap0441=true := by decide +kernel
theorem fusedMap0441_checked : acceptsGraphIso
    (fused (graph core0441) (root 6) 0 3) SmallGeFourSpectrum093.graph fusedMap0441=true := by decide +kernel
theorem certified0441 : Certified (graph core0441) (root 6) 0 3 :=
  of_native_maps core0441 SmallGeFourSpectrum121.graph SmallGeFourSpectrum093.graph
    sourceMap0441 fusedMap0441 sourceMap0441_checked fusedMap0441_checked
    DegreeOneSmallComparisons.comparison0441
#print axioms sourceMap0441_checked
#print axioms fusedMap0441_checked
#print axioms certified0441
def sourceMap0441swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,8] (sourceLabel 6 3 0 v)
def fusedMap0441swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0441swap_checked : acceptsGraphIso
    (source (graph core0441) (root 6) 3 0) SmallGeFourSpectrum121.graph sourceMap0441swap=true := by decide +kernel
theorem fusedMap0441swap_checked : acceptsGraphIso
    (fused (graph core0441) (root 6) 3 0) SmallGeFourSpectrum093.graph fusedMap0441swap=true := by decide +kernel
theorem certified0441swap : Certified (graph core0441) (root 6) 3 0 :=
  of_native_maps core0441 SmallGeFourSpectrum121.graph SmallGeFourSpectrum093.graph
    sourceMap0441swap fusedMap0441swap sourceMap0441swap_checked fusedMap0441swap_checked
    DegreeOneSmallComparisons.comparison0441
#print axioms sourceMap0441swap_checked
#print axioms fusedMap0441swap_checked
#print axioms certified0441swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
