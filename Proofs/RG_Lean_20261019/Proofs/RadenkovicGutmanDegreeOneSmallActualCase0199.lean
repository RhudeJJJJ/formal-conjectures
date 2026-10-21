/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0199 : Family 5 := level5.get ⟨3,by decide⟩
def sourceMap0199 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 5 0 4 v)
def fusedMap0199 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 0 4 v)
theorem sourceMap0199_checked : acceptsGraphIso
    (source (graph core0199) (root 5) 0 4) DegreeOneSmallSpectrum389.graph sourceMap0199=true := by decide +kernel
theorem fusedMap0199_checked : acceptsGraphIso
    (fused (graph core0199) (root 5) 0 4) DegreeOneSmallSpectrum392.graph fusedMap0199=true := by decide +kernel
theorem certified0199 : Certified (graph core0199) (root 5) 0 4 :=
  of_native_maps core0199 DegreeOneSmallSpectrum389.graph DegreeOneSmallSpectrum392.graph
    sourceMap0199 fusedMap0199 sourceMap0199_checked fusedMap0199_checked
    DegreeOneSmallComparisons.comparison0199
#print axioms sourceMap0199_checked
#print axioms fusedMap0199_checked
#print axioms certified0199
def sourceMap0199swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,7,8,9,10,11,6] (sourceLabel 5 4 0 v)
def fusedMap0199swap : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10,11] (fusedLabel 5 4 0 v)
theorem sourceMap0199swap_checked : acceptsGraphIso
    (source (graph core0199) (root 5) 4 0) DegreeOneSmallSpectrum389.graph sourceMap0199swap=true := by decide +kernel
theorem fusedMap0199swap_checked : acceptsGraphIso
    (fused (graph core0199) (root 5) 4 0) DegreeOneSmallSpectrum392.graph fusedMap0199swap=true := by decide +kernel
theorem certified0199swap : Certified (graph core0199) (root 5) 4 0 :=
  of_native_maps core0199 DegreeOneSmallSpectrum389.graph DegreeOneSmallSpectrum392.graph
    sourceMap0199swap fusedMap0199swap sourceMap0199swap_checked fusedMap0199swap_checked
    DegreeOneSmallComparisons.comparison0199
#print axioms sourceMap0199swap_checked
#print axioms fusedMap0199swap_checked
#print axioms certified0199swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
