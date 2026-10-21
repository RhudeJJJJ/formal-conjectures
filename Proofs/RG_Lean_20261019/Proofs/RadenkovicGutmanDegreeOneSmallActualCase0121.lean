/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0121 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0121 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (sourceLabel 4 1 4 v)
def fusedMap0121 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 1 4 v)
theorem sourceMap0121_checked : acceptsGraphIso
    (source (graph core0121) (root 4) 1 4) DegreeOneSmallSpectrum464.graph sourceMap0121=true := by decide +kernel
theorem fusedMap0121_checked : acceptsGraphIso
    (fused (graph core0121) (root 4) 1 4) DegreeOneSmallSpectrum378.graph fusedMap0121=true := by decide +kernel
theorem certified0121 : Certified (graph core0121) (root 4) 1 4 :=
  of_native_maps core0121 DegreeOneSmallSpectrum464.graph DegreeOneSmallSpectrum378.graph
    sourceMap0121 fusedMap0121 sourceMap0121_checked fusedMap0121_checked
    DegreeOneSmallComparisons.comparison0121
#print axioms sourceMap0121_checked
#print axioms fusedMap0121_checked
#print axioms certified0121
def sourceMap0121swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,2,3,4,5,0,8,9,10,11,6,7] (sourceLabel 4 4 1 v)
def fusedMap0121swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11] (fusedLabel 4 4 1 v)
theorem sourceMap0121swap_checked : acceptsGraphIso
    (source (graph core0121) (root 4) 4 1) DegreeOneSmallSpectrum464.graph sourceMap0121swap=true := by decide +kernel
theorem fusedMap0121swap_checked : acceptsGraphIso
    (fused (graph core0121) (root 4) 4 1) DegreeOneSmallSpectrum378.graph fusedMap0121swap=true := by decide +kernel
theorem certified0121swap : Certified (graph core0121) (root 4) 4 1 :=
  of_native_maps core0121 DegreeOneSmallSpectrum464.graph DegreeOneSmallSpectrum378.graph
    sourceMap0121swap fusedMap0121swap sourceMap0121swap_checked fusedMap0121swap_checked
    DegreeOneSmallComparisons.comparison0121
#print axioms sourceMap0121swap_checked
#print axioms fusedMap0121swap_checked
#print axioms certified0121swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
