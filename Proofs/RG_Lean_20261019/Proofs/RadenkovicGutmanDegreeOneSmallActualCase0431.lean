/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0431 : Family 6 := level6.get ⟨29,by decide⟩
def sourceMap0431 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0431 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0431_checked : acceptsGraphIso
    (source (graph core0431) (root 6) 0 2) SmallGeFourSpectrum065.graph sourceMap0431=true := by decide +kernel
theorem fusedMap0431_checked : acceptsGraphIso
    (fused (graph core0431) (root 6) 0 2) SmallGeFourSpectrum038.graph fusedMap0431=true := by decide +kernel
theorem certified0431 : Certified (graph core0431) (root 6) 0 2 :=
  of_native_maps core0431 SmallGeFourSpectrum065.graph SmallGeFourSpectrum038.graph
    sourceMap0431 fusedMap0431 sourceMap0431_checked fusedMap0431_checked
    DegreeOneSmallComparisons.comparison0431
#print axioms sourceMap0431_checked
#print axioms fusedMap0431_checked
#print axioms certified0431
def sourceMap0431swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0431swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0431swap_checked : acceptsGraphIso
    (source (graph core0431) (root 6) 2 0) SmallGeFourSpectrum065.graph sourceMap0431swap=true := by decide +kernel
theorem fusedMap0431swap_checked : acceptsGraphIso
    (fused (graph core0431) (root 6) 2 0) SmallGeFourSpectrum038.graph fusedMap0431swap=true := by decide +kernel
theorem certified0431swap : Certified (graph core0431) (root 6) 2 0 :=
  of_native_maps core0431 SmallGeFourSpectrum065.graph SmallGeFourSpectrum038.graph
    sourceMap0431swap fusedMap0431swap sourceMap0431swap_checked fusedMap0431swap_checked
    DegreeOneSmallComparisons.comparison0431
#print axioms sourceMap0431swap_checked
#print axioms fusedMap0431swap_checked
#print axioms certified0431swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
