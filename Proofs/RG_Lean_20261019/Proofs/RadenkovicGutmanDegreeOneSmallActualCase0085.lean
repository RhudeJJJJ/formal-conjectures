/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0085 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0085 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (sourceLabel 3 1 3 v)
def fusedMap0085 : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (fusedLabel 3 1 3 v)
theorem sourceMap0085_checked : acceptsGraphIso
    (source (graph core0085) (root 3) 1 3) DegreeOneSmallSpectrum111.graph sourceMap0085=true := by decide +kernel
theorem fusedMap0085_checked : acceptsGraphIso
    (fused (graph core0085) (root 3) 1 3) DegreeOneSmallSpectrum080.graph fusedMap0085=true := by decide +kernel
theorem certified0085 : Certified (graph core0085) (root 3) 1 3 :=
  of_native_maps core0085 DegreeOneSmallSpectrum111.graph DegreeOneSmallSpectrum080.graph
    sourceMap0085 fusedMap0085 sourceMap0085_checked fusedMap0085_checked
    DegreeOneSmallComparisons.comparison0085
#print axioms sourceMap0085_checked
#print axioms fusedMap0085_checked
#print axioms certified0085
def sourceMap0085swap : (Vertices 3 ⊕ Fin 4 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,2,3,4,0,7,8,9,5,6] (sourceLabel 3 3 1 v)
def fusedMap0085swap : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (fusedLabel 3 3 1 v)
theorem sourceMap0085swap_checked : acceptsGraphIso
    (source (graph core0085) (root 3) 3 1) DegreeOneSmallSpectrum111.graph sourceMap0085swap=true := by decide +kernel
theorem fusedMap0085swap_checked : acceptsGraphIso
    (fused (graph core0085) (root 3) 3 1) DegreeOneSmallSpectrum080.graph fusedMap0085swap=true := by decide +kernel
theorem certified0085swap : Certified (graph core0085) (root 3) 3 1 :=
  of_native_maps core0085 DegreeOneSmallSpectrum111.graph DegreeOneSmallSpectrum080.graph
    sourceMap0085swap fusedMap0085swap sourceMap0085swap_checked fusedMap0085swap_checked
    DegreeOneSmallComparisons.comparison0085
#print axioms sourceMap0085swap_checked
#print axioms fusedMap0085swap_checked
#print axioms certified0085swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
