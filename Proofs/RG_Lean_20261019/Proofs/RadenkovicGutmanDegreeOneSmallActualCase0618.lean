/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0618 : Family 7 := level7.get ⟨40,by decide⟩
def sourceMap0618 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0618 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0618_checked : acceptsGraphIso
    (source (graph core0618) (root 7) 0 3) DegreeOneSmallSpectrum1331.graph sourceMap0618=true := by decide +kernel
theorem fusedMap0618_checked : acceptsGraphIso
    (fused (graph core0618) (root 7) 0 3) DegreeOneSmallSpectrum910.graph fusedMap0618=true := by decide +kernel
theorem certified0618 : Certified (graph core0618) (root 7) 0 3 :=
  of_native_maps core0618 DegreeOneSmallSpectrum1331.graph DegreeOneSmallSpectrum910.graph
    sourceMap0618 fusedMap0618 sourceMap0618_checked fusedMap0618_checked
    DegreeOneSmallComparisons.comparison0618
#print axioms sourceMap0618_checked
#print axioms fusedMap0618_checked
#print axioms certified0618
def sourceMap0618swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0618swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0618swap_checked : acceptsGraphIso
    (source (graph core0618) (root 7) 3 0) DegreeOneSmallSpectrum1331.graph sourceMap0618swap=true := by decide +kernel
theorem fusedMap0618swap_checked : acceptsGraphIso
    (fused (graph core0618) (root 7) 3 0) DegreeOneSmallSpectrum910.graph fusedMap0618swap=true := by decide +kernel
theorem certified0618swap : Certified (graph core0618) (root 7) 3 0 :=
  of_native_maps core0618 DegreeOneSmallSpectrum1331.graph DegreeOneSmallSpectrum910.graph
    sourceMap0618swap fusedMap0618swap sourceMap0618swap_checked fusedMap0618swap_checked
    DegreeOneSmallComparisons.comparison0618
#print axioms sourceMap0618swap_checked
#print axioms fusedMap0618swap_checked
#print axioms certified0618swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
