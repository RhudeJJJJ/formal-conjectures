/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0185 : Family 5 := level5.get ⟨2,by decide⟩
def sourceMap0185 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,9,6,7,8] (sourceLabel 5 0 2 v)
def fusedMap0185 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap0185_checked : acceptsGraphIso
    (source (graph core0185) (root 5) 0 2) DegreeOneSmallSpectrum085.graph sourceMap0185=true := by decide +kernel
theorem fusedMap0185_checked : acceptsGraphIso
    (fused (graph core0185) (root 5) 0 2) DegreeOneSmallSpectrum086.graph fusedMap0185=true := by decide +kernel
theorem certified0185 : Certified (graph core0185) (root 5) 0 2 :=
  of_native_maps core0185 DegreeOneSmallSpectrum085.graph DegreeOneSmallSpectrum086.graph
    sourceMap0185 fusedMap0185 sourceMap0185_checked fusedMap0185_checked
    DegreeOneSmallComparisons.comparison0185
#print axioms sourceMap0185_checked
#print axioms fusedMap0185_checked
#print axioms certified0185
def sourceMap0185swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9] (sourceLabel 5 2 0 v)
def fusedMap0185swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap0185swap_checked : acceptsGraphIso
    (source (graph core0185) (root 5) 2 0) DegreeOneSmallSpectrum085.graph sourceMap0185swap=true := by decide +kernel
theorem fusedMap0185swap_checked : acceptsGraphIso
    (fused (graph core0185) (root 5) 2 0) DegreeOneSmallSpectrum086.graph fusedMap0185swap=true := by decide +kernel
theorem certified0185swap : Certified (graph core0185) (root 5) 2 0 :=
  of_native_maps core0185 DegreeOneSmallSpectrum085.graph DegreeOneSmallSpectrum086.graph
    sourceMap0185swap fusedMap0185swap sourceMap0185swap_checked fusedMap0185swap_checked
    DegreeOneSmallComparisons.comparison0185
#print axioms sourceMap0185swap_checked
#print axioms fusedMap0185swap_checked
#print axioms certified0185swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
