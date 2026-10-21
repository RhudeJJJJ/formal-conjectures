/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0047 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0047 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,4,5,1,2,3,6,7,8,9] (sourceLabel 2 2 3 v)
def fusedMap0047 : (Vertices 2 ⊕ Fin 7) → Fin 10 :=
  fun v => ![2,3,4,1,0,5,6,7,8,9] (fusedLabel 2 2 3 v)
theorem sourceMap0047_checked : acceptsGraphIso
    (source (graph core0047) (root 2) 2 3) DegreeOneSmallSpectrum087.graph sourceMap0047=true := by decide +kernel
theorem fusedMap0047_checked : acceptsGraphIso
    (fused (graph core0047) (root 2) 2 3) DegreeOneSmallSpectrum073.graph fusedMap0047=true := by decide +kernel
theorem certified0047 : Certified (graph core0047) (root 2) 2 3 :=
  of_native_maps core0047 DegreeOneSmallSpectrum087.graph DegreeOneSmallSpectrum073.graph
    sourceMap0047 fusedMap0047 sourceMap0047_checked fusedMap0047_checked
    DegreeOneSmallComparisons.comparison0047
#print axioms sourceMap0047_checked
#print axioms fusedMap0047_checked
#print axioms certified0047
def sourceMap0047swap : (Vertices 2 ⊕ Fin 4 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,4,5,6,7,8,9,1,2,3] (sourceLabel 2 3 2 v)
def fusedMap0047swap : (Vertices 2 ⊕ Fin 7) → Fin 10 :=
  fun v => ![2,3,4,1,0,5,6,7,8,9] (fusedLabel 2 3 2 v)
theorem sourceMap0047swap_checked : acceptsGraphIso
    (source (graph core0047) (root 2) 3 2) DegreeOneSmallSpectrum087.graph sourceMap0047swap=true := by decide +kernel
theorem fusedMap0047swap_checked : acceptsGraphIso
    (fused (graph core0047) (root 2) 3 2) DegreeOneSmallSpectrum073.graph fusedMap0047swap=true := by decide +kernel
theorem certified0047swap : Certified (graph core0047) (root 2) 3 2 :=
  of_native_maps core0047 DegreeOneSmallSpectrum087.graph DegreeOneSmallSpectrum073.graph
    sourceMap0047swap fusedMap0047swap sourceMap0047swap_checked fusedMap0047swap_checked
    DegreeOneSmallComparisons.comparison0047
#print axioms sourceMap0047swap_checked
#print axioms fusedMap0047swap_checked
#print axioms certified0047swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
