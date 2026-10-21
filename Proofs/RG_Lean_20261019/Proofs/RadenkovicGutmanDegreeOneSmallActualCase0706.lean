/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0706 : Family 7 := level7.get ⟨73,by decide⟩
def sourceMap0706 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0706 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0706_checked : acceptsGraphIso
    (source (graph core0706) (root 7) 0 1) DegreeOneSmallSpectrum284.graph sourceMap0706=true := by decide +kernel
theorem fusedMap0706_checked : acceptsGraphIso
    (fused (graph core0706) (root 7) 0 1) SmallGeFourSpectrum049.graph fusedMap0706=true := by decide +kernel
theorem certified0706 : Certified (graph core0706) (root 7) 0 1 :=
  of_native_maps core0706 DegreeOneSmallSpectrum284.graph SmallGeFourSpectrum049.graph
    sourceMap0706 fusedMap0706 sourceMap0706_checked fusedMap0706_checked
    DegreeOneSmallComparisons.comparison0706
#print axioms sourceMap0706_checked
#print axioms fusedMap0706_checked
#print axioms certified0706
def sourceMap0706swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0706swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0706swap_checked : acceptsGraphIso
    (source (graph core0706) (root 7) 1 0) DegreeOneSmallSpectrum284.graph sourceMap0706swap=true := by decide +kernel
theorem fusedMap0706swap_checked : acceptsGraphIso
    (fused (graph core0706) (root 7) 1 0) SmallGeFourSpectrum049.graph fusedMap0706swap=true := by decide +kernel
theorem certified0706swap : Certified (graph core0706) (root 7) 1 0 :=
  of_native_maps core0706 DegreeOneSmallSpectrum284.graph SmallGeFourSpectrum049.graph
    sourceMap0706swap fusedMap0706swap sourceMap0706swap_checked fusedMap0706swap_checked
    DegreeOneSmallComparisons.comparison0706
#print axioms sourceMap0706swap_checked
#print axioms fusedMap0706swap_checked
#print axioms certified0706swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
