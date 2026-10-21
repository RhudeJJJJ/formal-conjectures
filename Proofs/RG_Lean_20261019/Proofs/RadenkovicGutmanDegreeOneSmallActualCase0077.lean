/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0077 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0077 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (sourceLabel 3 0 2 v)
def fusedMap0077 : (Vertices 3 ⊕ Fin 4) → Fin 8 :=
  fun v => ![1,2,3,4,0,5,6,7] (fusedLabel 3 0 2 v)
theorem sourceMap0077_checked : acceptsGraphIso
    (source (graph core0077) (root 3) 0 2) DegreeOneSmallSpectrum018.graph sourceMap0077=true := by decide +kernel
theorem fusedMap0077_checked : acceptsGraphIso
    (fused (graph core0077) (root 3) 0 2) DegreeOneSmallSpectrum021.graph fusedMap0077=true := by decide +kernel
theorem certified0077 : Certified (graph core0077) (root 3) 0 2 :=
  of_native_maps core0077 DegreeOneSmallSpectrum018.graph DegreeOneSmallSpectrum021.graph
    sourceMap0077 fusedMap0077 sourceMap0077_checked fusedMap0077_checked
    DegreeOneSmallComparisons.comparison0077
#print axioms sourceMap0077_checked
#print axioms fusedMap0077_checked
#print axioms certified0077
def sourceMap0077swap : (Vertices 3 ⊕ Fin 3 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,1,2,3,5,6,7,4] (sourceLabel 3 2 0 v)
def fusedMap0077swap : (Vertices 3 ⊕ Fin 4) → Fin 8 :=
  fun v => ![1,2,3,4,0,5,6,7] (fusedLabel 3 2 0 v)
theorem sourceMap0077swap_checked : acceptsGraphIso
    (source (graph core0077) (root 3) 2 0) DegreeOneSmallSpectrum018.graph sourceMap0077swap=true := by decide +kernel
theorem fusedMap0077swap_checked : acceptsGraphIso
    (fused (graph core0077) (root 3) 2 0) DegreeOneSmallSpectrum021.graph fusedMap0077swap=true := by decide +kernel
theorem certified0077swap : Certified (graph core0077) (root 3) 2 0 :=
  of_native_maps core0077 DegreeOneSmallSpectrum018.graph DegreeOneSmallSpectrum021.graph
    sourceMap0077swap fusedMap0077swap sourceMap0077swap_checked fusedMap0077swap_checked
    DegreeOneSmallComparisons.comparison0077
#print axioms sourceMap0077swap_checked
#print axioms fusedMap0077swap_checked
#print axioms certified0077swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
