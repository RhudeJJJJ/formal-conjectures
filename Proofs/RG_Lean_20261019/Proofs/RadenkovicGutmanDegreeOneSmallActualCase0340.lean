/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0340 : Family 6 := level6.get ⟨10,by decide⟩
def sourceMap0340 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (sourceLabel 6 0 1 v)
def fusedMap0340 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0340_checked : acceptsGraphIso
    (source (graph core0340) (root 6) 0 1) DegreeOneSmallSpectrum136.graph sourceMap0340=true := by decide +kernel
theorem fusedMap0340_checked : acceptsGraphIso
    (fused (graph core0340) (root 6) 0 1) DegreeOneSmallSpectrum081.graph fusedMap0340=true := by decide +kernel
theorem certified0340 : Certified (graph core0340) (root 6) 0 1 :=
  of_native_maps core0340 DegreeOneSmallSpectrum136.graph DegreeOneSmallSpectrum081.graph
    sourceMap0340 fusedMap0340 sourceMap0340_checked fusedMap0340_checked
    DegreeOneSmallComparisons.comparison0340
#print axioms sourceMap0340_checked
#print axioms fusedMap0340_checked
#print axioms certified0340
def sourceMap0340swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (sourceLabel 6 1 0 v)
def fusedMap0340swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0340swap_checked : acceptsGraphIso
    (source (graph core0340) (root 6) 1 0) DegreeOneSmallSpectrum136.graph sourceMap0340swap=true := by decide +kernel
theorem fusedMap0340swap_checked : acceptsGraphIso
    (fused (graph core0340) (root 6) 1 0) DegreeOneSmallSpectrum081.graph fusedMap0340swap=true := by decide +kernel
theorem certified0340swap : Certified (graph core0340) (root 6) 1 0 :=
  of_native_maps core0340 DegreeOneSmallSpectrum136.graph DegreeOneSmallSpectrum081.graph
    sourceMap0340swap fusedMap0340swap sourceMap0340swap_checked fusedMap0340swap_checked
    DegreeOneSmallComparisons.comparison0340
#print axioms sourceMap0340swap_checked
#print axioms fusedMap0340swap_checked
#print axioms certified0340swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
