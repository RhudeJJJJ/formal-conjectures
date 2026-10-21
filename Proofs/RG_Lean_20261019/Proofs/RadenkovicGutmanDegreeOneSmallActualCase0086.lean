/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0086 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0086 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (sourceLabel 3 1 4 v)
def fusedMap0086 : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 1 4 v)
theorem sourceMap0086_checked : acceptsGraphIso
    (source (graph core0086) (root 3) 1 4) DegreeOneSmallSpectrum176.graph sourceMap0086=true := by decide +kernel
theorem fusedMap0086_checked : acceptsGraphIso
    (fused (graph core0086) (root 3) 1 4) DegreeOneSmallSpectrum164.graph fusedMap0086=true := by decide +kernel
theorem certified0086 : Certified (graph core0086) (root 3) 1 4 :=
  of_native_maps core0086 DegreeOneSmallSpectrum176.graph DegreeOneSmallSpectrum164.graph
    sourceMap0086 fusedMap0086 sourceMap0086_checked fusedMap0086_checked
    DegreeOneSmallComparisons.comparison0086
#print axioms sourceMap0086_checked
#print axioms fusedMap0086_checked
#print axioms certified0086
def sourceMap0086swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,2,3,4,0,7,8,9,10,5,6] (sourceLabel 3 4 1 v)
def fusedMap0086swap : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 4 1 v)
theorem sourceMap0086swap_checked : acceptsGraphIso
    (source (graph core0086) (root 3) 4 1) DegreeOneSmallSpectrum176.graph sourceMap0086swap=true := by decide +kernel
theorem fusedMap0086swap_checked : acceptsGraphIso
    (fused (graph core0086) (root 3) 4 1) DegreeOneSmallSpectrum164.graph fusedMap0086swap=true := by decide +kernel
theorem certified0086swap : Certified (graph core0086) (root 3) 4 1 :=
  of_native_maps core0086 DegreeOneSmallSpectrum176.graph DegreeOneSmallSpectrum164.graph
    sourceMap0086swap fusedMap0086swap sourceMap0086swap_checked fusedMap0086swap_checked
    DegreeOneSmallComparisons.comparison0086
#print axioms sourceMap0086swap_checked
#print axioms fusedMap0086swap_checked
#print axioms certified0086swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
