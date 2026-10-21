/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0278 : Family 6 := level6.get ⟨1,by decide⟩
def sourceMap0278 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0278 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0278_checked : acceptsGraphIso
    (source (graph core0278) (root 6) 0 2) DegreeOneSmallSpectrum196.graph sourceMap0278=true := by decide +kernel
theorem fusedMap0278_checked : acceptsGraphIso
    (fused (graph core0278) (root 6) 0 2) DegreeOneSmallSpectrum164.graph fusedMap0278=true := by decide +kernel
theorem certified0278 : Certified (graph core0278) (root 6) 0 2 :=
  of_native_maps core0278 DegreeOneSmallSpectrum196.graph DegreeOneSmallSpectrum164.graph
    sourceMap0278 fusedMap0278 sourceMap0278_checked fusedMap0278_checked
    DegreeOneSmallComparisons.comparison0278
#print axioms sourceMap0278_checked
#print axioms fusedMap0278_checked
#print axioms certified0278
def sourceMap0278swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0278swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0278swap_checked : acceptsGraphIso
    (source (graph core0278) (root 6) 2 0) DegreeOneSmallSpectrum196.graph sourceMap0278swap=true := by decide +kernel
theorem fusedMap0278swap_checked : acceptsGraphIso
    (fused (graph core0278) (root 6) 2 0) DegreeOneSmallSpectrum164.graph fusedMap0278swap=true := by decide +kernel
theorem certified0278swap : Certified (graph core0278) (root 6) 2 0 :=
  of_native_maps core0278 DegreeOneSmallSpectrum196.graph DegreeOneSmallSpectrum164.graph
    sourceMap0278swap fusedMap0278swap sourceMap0278swap_checked fusedMap0278swap_checked
    DegreeOneSmallComparisons.comparison0278
#print axioms sourceMap0278swap_checked
#print axioms fusedMap0278swap_checked
#print axioms certified0278swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
