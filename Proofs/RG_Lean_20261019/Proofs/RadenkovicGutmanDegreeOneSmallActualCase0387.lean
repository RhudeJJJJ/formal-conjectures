/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0387 : Family 6 := level6.get ⟨19,by decide⟩
def sourceMap0387 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 0 3 v)
def fusedMap0387 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0387_checked : acceptsGraphIso
    (source (graph core0387) (root 6) 0 3) DegreeOneSmallSpectrum400.graph sourceMap0387=true := by decide +kernel
theorem fusedMap0387_checked : acceptsGraphIso
    (fused (graph core0387) (root 6) 0 3) SmallGeFourSpectrum094.graph fusedMap0387=true := by decide +kernel
theorem certified0387 : Certified (graph core0387) (root 6) 0 3 :=
  of_native_maps core0387 DegreeOneSmallSpectrum400.graph SmallGeFourSpectrum094.graph
    sourceMap0387 fusedMap0387 sourceMap0387_checked fusedMap0387_checked
    DegreeOneSmallComparisons.comparison0387
#print axioms sourceMap0387_checked
#print axioms fusedMap0387_checked
#print axioms certified0387
def sourceMap0387swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,7] (sourceLabel 6 3 0 v)
def fusedMap0387swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0387swap_checked : acceptsGraphIso
    (source (graph core0387) (root 6) 3 0) DegreeOneSmallSpectrum400.graph sourceMap0387swap=true := by decide +kernel
theorem fusedMap0387swap_checked : acceptsGraphIso
    (fused (graph core0387) (root 6) 3 0) SmallGeFourSpectrum094.graph fusedMap0387swap=true := by decide +kernel
theorem certified0387swap : Certified (graph core0387) (root 6) 3 0 :=
  of_native_maps core0387 DegreeOneSmallSpectrum400.graph SmallGeFourSpectrum094.graph
    sourceMap0387swap fusedMap0387swap sourceMap0387swap_checked fusedMap0387swap_checked
    DegreeOneSmallComparisons.comparison0387
#print axioms sourceMap0387swap_checked
#print axioms fusedMap0387swap_checked
#print axioms certified0387swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
