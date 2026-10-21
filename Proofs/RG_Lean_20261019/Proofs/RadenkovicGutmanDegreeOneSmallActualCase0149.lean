/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0149 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0149 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (sourceLabel 4 0 6 v)
def fusedMap0149 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 0 6 v)
theorem sourceMap0149_checked : acceptsGraphIso
    (source (graph core0149) (root 4) 0 6) DegreeOneSmallSpectrum863.graph sourceMap0149=true := by decide +kernel
theorem fusedMap0149_checked : acceptsGraphIso
    (fused (graph core0149) (root 4) 0 6) DegreeOneSmallSpectrum870.graph fusedMap0149=true := by decide +kernel
theorem certified0149 : Certified (graph core0149) (root 4) 0 6 :=
  of_native_maps core0149 DegreeOneSmallSpectrum863.graph DegreeOneSmallSpectrum870.graph
    sourceMap0149 fusedMap0149 sourceMap0149_checked fusedMap0149_checked
    DegreeOneSmallComparisons.comparison0149
#print axioms sourceMap0149_checked
#print axioms fusedMap0149_checked
#print axioms certified0149
def sourceMap0149swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,11,12,7] (sourceLabel 4 6 0 v)
def fusedMap0149swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 6 0 v)
theorem sourceMap0149swap_checked : acceptsGraphIso
    (source (graph core0149) (root 4) 6 0) DegreeOneSmallSpectrum863.graph sourceMap0149swap=true := by decide +kernel
theorem fusedMap0149swap_checked : acceptsGraphIso
    (fused (graph core0149) (root 4) 6 0) DegreeOneSmallSpectrum870.graph fusedMap0149swap=true := by decide +kernel
theorem certified0149swap : Certified (graph core0149) (root 4) 6 0 :=
  of_native_maps core0149 DegreeOneSmallSpectrum863.graph DegreeOneSmallSpectrum870.graph
    sourceMap0149swap fusedMap0149swap sourceMap0149swap_checked fusedMap0149swap_checked
    DegreeOneSmallComparisons.comparison0149
#print axioms sourceMap0149swap_checked
#print axioms fusedMap0149swap_checked
#print axioms certified0149swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
