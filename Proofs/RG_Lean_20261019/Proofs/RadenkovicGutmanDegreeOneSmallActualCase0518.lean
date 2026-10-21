/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0518 : Family 7 := level7.get ⟨13,by decide⟩
def sourceMap0518 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0518 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0518_checked : acceptsGraphIso
    (source (graph core0518) (root 7) 1 2) DegreeOneSmallSpectrum1388.graph sourceMap0518=true := by decide +kernel
theorem fusedMap0518_checked : acceptsGraphIso
    (fused (graph core0518) (root 7) 1 2) DegreeOneSmallSpectrum922.graph fusedMap0518=true := by decide +kernel
theorem certified0518 : Certified (graph core0518) (root 7) 1 2 :=
  of_native_maps core0518 DegreeOneSmallSpectrum1388.graph DegreeOneSmallSpectrum922.graph
    sourceMap0518 fusedMap0518 sourceMap0518_checked fusedMap0518_checked
    DegreeOneSmallComparisons.comparison0518
#print axioms sourceMap0518_checked
#print axioms fusedMap0518_checked
#print axioms certified0518
def sourceMap0518swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0518swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0518swap_checked : acceptsGraphIso
    (source (graph core0518) (root 7) 2 1) DegreeOneSmallSpectrum1388.graph sourceMap0518swap=true := by decide +kernel
theorem fusedMap0518swap_checked : acceptsGraphIso
    (fused (graph core0518) (root 7) 2 1) DegreeOneSmallSpectrum922.graph fusedMap0518swap=true := by decide +kernel
theorem certified0518swap : Certified (graph core0518) (root 7) 2 1 :=
  of_native_maps core0518 DegreeOneSmallSpectrum1388.graph DegreeOneSmallSpectrum922.graph
    sourceMap0518swap fusedMap0518swap sourceMap0518swap_checked fusedMap0518swap_checked
    DegreeOneSmallComparisons.comparison0518
#print axioms sourceMap0518swap_checked
#print axioms fusedMap0518swap_checked
#print axioms certified0518swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
