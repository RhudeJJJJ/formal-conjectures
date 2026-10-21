/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0432 : Family 6 := level6.get ⟨29,by decide⟩
def sourceMap0432 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 0 3 v)
def fusedMap0432 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0432_checked : acceptsGraphIso
    (source (graph core0432) (root 6) 0 3) SmallGeFourSpectrum101.graph sourceMap0432=true := by decide +kernel
theorem fusedMap0432_checked : acceptsGraphIso
    (fused (graph core0432) (root 6) 0 3) SmallGeFourSpectrum104.graph fusedMap0432=true := by decide +kernel
theorem certified0432 : Certified (graph core0432) (root 6) 0 3 :=
  of_native_maps core0432 SmallGeFourSpectrum101.graph SmallGeFourSpectrum104.graph
    sourceMap0432 fusedMap0432 sourceMap0432_checked fusedMap0432_checked
    DegreeOneSmallComparisons.comparison0432
#print axioms sourceMap0432_checked
#print axioms fusedMap0432_checked
#print axioms certified0432
def sourceMap0432swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,7] (sourceLabel 6 3 0 v)
def fusedMap0432swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0432swap_checked : acceptsGraphIso
    (source (graph core0432) (root 6) 3 0) SmallGeFourSpectrum101.graph sourceMap0432swap=true := by decide +kernel
theorem fusedMap0432swap_checked : acceptsGraphIso
    (fused (graph core0432) (root 6) 3 0) SmallGeFourSpectrum104.graph fusedMap0432swap=true := by decide +kernel
theorem certified0432swap : Certified (graph core0432) (root 6) 3 0 :=
  of_native_maps core0432 SmallGeFourSpectrum101.graph SmallGeFourSpectrum104.graph
    sourceMap0432swap fusedMap0432swap sourceMap0432swap_checked fusedMap0432swap_checked
    DegreeOneSmallComparisons.comparison0432
#print axioms sourceMap0432swap_checked
#print axioms fusedMap0432swap_checked
#print axioms certified0432swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
