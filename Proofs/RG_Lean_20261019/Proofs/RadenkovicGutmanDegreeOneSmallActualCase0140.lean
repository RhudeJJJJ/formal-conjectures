/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0140 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0140 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 4 2 3 v)
def fusedMap0140 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 2 3 v)
theorem sourceMap0140_checked : acceptsGraphIso
    (source (graph core0140) (root 4) 2 3) DegreeOneSmallSpectrum535.graph sourceMap0140=true := by decide +kernel
theorem fusedMap0140_checked : acceptsGraphIso
    (fused (graph core0140) (root 4) 2 3) DegreeOneSmallSpectrum386.graph fusedMap0140=true := by decide +kernel
theorem certified0140 : Certified (graph core0140) (root 4) 2 3 :=
  of_native_maps core0140 DegreeOneSmallSpectrum535.graph DegreeOneSmallSpectrum386.graph
    sourceMap0140 fusedMap0140 sourceMap0140_checked fusedMap0140_checked
    DegreeOneSmallComparisons.comparison0140
#print axioms sourceMap0140_checked
#print axioms fusedMap0140_checked
#print axioms certified0140
def sourceMap0140swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (sourceLabel 4 3 2 v)
def fusedMap0140swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 3 2 v)
theorem sourceMap0140swap_checked : acceptsGraphIso
    (source (graph core0140) (root 4) 3 2) DegreeOneSmallSpectrum535.graph sourceMap0140swap=true := by decide +kernel
theorem fusedMap0140swap_checked : acceptsGraphIso
    (fused (graph core0140) (root 4) 3 2) DegreeOneSmallSpectrum386.graph fusedMap0140swap=true := by decide +kernel
theorem certified0140swap : Certified (graph core0140) (root 4) 3 2 :=
  of_native_maps core0140 DegreeOneSmallSpectrum535.graph DegreeOneSmallSpectrum386.graph
    sourceMap0140swap fusedMap0140swap sourceMap0140swap_checked fusedMap0140swap_checked
    DegreeOneSmallComparisons.comparison0140
#print axioms sourceMap0140swap_checked
#print axioms fusedMap0140swap_checked
#print axioms certified0140swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
