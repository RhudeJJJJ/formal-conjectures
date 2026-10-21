/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0315 : Family 6 := level6.get ⟨6,by decide⟩
def sourceMap0315 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (sourceLabel 6 0 3 v)
def fusedMap0315 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0315_checked : acceptsGraphIso
    (source (graph core0315) (root 6) 0 3) DegreeOneSmallSpectrum427.graph sourceMap0315=true := by decide +kernel
theorem fusedMap0315_checked : acceptsGraphIso
    (fused (graph core0315) (root 6) 0 3) DegreeOneSmallSpectrum370.graph fusedMap0315=true := by decide +kernel
theorem certified0315 : Certified (graph core0315) (root 6) 0 3 :=
  of_native_maps core0315 DegreeOneSmallSpectrum427.graph DegreeOneSmallSpectrum370.graph
    sourceMap0315 fusedMap0315 sourceMap0315_checked fusedMap0315_checked
    DegreeOneSmallComparisons.comparison0315
#print axioms sourceMap0315_checked
#print axioms fusedMap0315_checked
#print axioms certified0315
def sourceMap0315swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 3 0 v)
def fusedMap0315swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0315swap_checked : acceptsGraphIso
    (source (graph core0315) (root 6) 3 0) DegreeOneSmallSpectrum427.graph sourceMap0315swap=true := by decide +kernel
theorem fusedMap0315swap_checked : acceptsGraphIso
    (fused (graph core0315) (root 6) 3 0) DegreeOneSmallSpectrum370.graph fusedMap0315swap=true := by decide +kernel
theorem certified0315swap : Certified (graph core0315) (root 6) 3 0 :=
  of_native_maps core0315 DegreeOneSmallSpectrum427.graph DegreeOneSmallSpectrum370.graph
    sourceMap0315swap fusedMap0315swap sourceMap0315swap_checked fusedMap0315swap_checked
    DegreeOneSmallComparisons.comparison0315
#print axioms sourceMap0315swap_checked
#print axioms fusedMap0315swap_checked
#print axioms certified0315swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
