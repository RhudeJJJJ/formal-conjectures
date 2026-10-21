/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0076 : Family 3 := level3.get ⟨1,by decide⟩
def sourceMap0076 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 2) → Fin 7 :=
  fun v => ![0,1,2,3,6,4,5] (sourceLabel 3 0 1 v)
def fusedMap0076 : (Vertices 3 ⊕ Fin 3) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (fusedLabel 3 0 1 v)
theorem sourceMap0076_checked : acceptsGraphIso
    (source (graph core0076) (root 3) 0 1) DegreeOneSmallSpectrum014.graph sourceMap0076=true := by decide +kernel
theorem fusedMap0076_checked : acceptsGraphIso
    (fused (graph core0076) (root 3) 0 1) DegreeOneSmallSpectrum008.graph fusedMap0076=true := by decide +kernel
theorem certified0076 : Certified (graph core0076) (root 3) 0 1 :=
  of_native_maps core0076 DegreeOneSmallSpectrum014.graph DegreeOneSmallSpectrum008.graph
    sourceMap0076 fusedMap0076 sourceMap0076_checked fusedMap0076_checked
    DegreeOneSmallComparisons.comparison0076
#print axioms sourceMap0076_checked
#print axioms fusedMap0076_checked
#print axioms certified0076
def sourceMap0076swap : (Vertices 3 ⊕ Fin 2 ⊕ Fin 1) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (sourceLabel 3 1 0 v)
def fusedMap0076swap : (Vertices 3 ⊕ Fin 3) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (fusedLabel 3 1 0 v)
theorem sourceMap0076swap_checked : acceptsGraphIso
    (source (graph core0076) (root 3) 1 0) DegreeOneSmallSpectrum014.graph sourceMap0076swap=true := by decide +kernel
theorem fusedMap0076swap_checked : acceptsGraphIso
    (fused (graph core0076) (root 3) 1 0) DegreeOneSmallSpectrum008.graph fusedMap0076swap=true := by decide +kernel
theorem certified0076swap : Certified (graph core0076) (root 3) 1 0 :=
  of_native_maps core0076 DegreeOneSmallSpectrum014.graph DegreeOneSmallSpectrum008.graph
    sourceMap0076swap fusedMap0076swap sourceMap0076swap_checked fusedMap0076swap_checked
    DegreeOneSmallComparisons.comparison0076
#print axioms sourceMap0076swap_checked
#print axioms fusedMap0076swap_checked
#print axioms certified0076swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
