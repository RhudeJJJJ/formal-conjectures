/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0080 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0080 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (sourceLabel 3 0 5 v)
def fusedMap0080 : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 0 5 v)
theorem sourceMap0080_checked : acceptsGraphIso
    (source (graph core0080) (root 3) 0 5) DegreeOneSmallSpectrum182.graph sourceMap0080=true := by decide +kernel
theorem fusedMap0080_checked : acceptsGraphIso
    (fused (graph core0080) (root 3) 0 5) DegreeOneSmallSpectrum164.graph fusedMap0080=true := by decide +kernel
theorem certified0080 : Certified (graph core0080) (root 3) 0 5 :=
  of_native_maps core0080 DegreeOneSmallSpectrum182.graph DegreeOneSmallSpectrum164.graph
    sourceMap0080 fusedMap0080 sourceMap0080_checked fusedMap0080_checked
    DegreeOneSmallComparisons.comparison0080
#print axioms sourceMap0080_checked
#print axioms fusedMap0080_checked
#print axioms certified0080
def sourceMap0080swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,7,8,9,10,6] (sourceLabel 3 5 0 v)
def fusedMap0080swap : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 5 0 v)
theorem sourceMap0080swap_checked : acceptsGraphIso
    (source (graph core0080) (root 3) 5 0) DegreeOneSmallSpectrum182.graph sourceMap0080swap=true := by decide +kernel
theorem fusedMap0080swap_checked : acceptsGraphIso
    (fused (graph core0080) (root 3) 5 0) DegreeOneSmallSpectrum164.graph fusedMap0080swap=true := by decide +kernel
theorem certified0080swap : Certified (graph core0080) (root 3) 5 0 :=
  of_native_maps core0080 DegreeOneSmallSpectrum182.graph DegreeOneSmallSpectrum164.graph
    sourceMap0080swap fusedMap0080swap sourceMap0080swap_checked fusedMap0080swap_checked
    DegreeOneSmallComparisons.comparison0080
#print axioms sourceMap0080swap_checked
#print axioms fusedMap0080swap_checked
#print axioms certified0080swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
