/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0968 : Family 8 := level8.get ⟨83,by decide⟩
def sourceMap0968 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0968 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (fusedLabel 8 0 1 v)
theorem sourceMap0968_checked : acceptsGraphIso
    (source (graph core0968) (root 8) 0 1) DegreeOneSmallSpectrum535.graph sourceMap0968=true := by decide +kernel
theorem fusedMap0968_checked : acceptsGraphIso
    (fused (graph core0968) (root 8) 0 1) DegreeOneSmallSpectrum585.graph fusedMap0968=true := by decide +kernel
theorem certified0968 : Certified (graph core0968) (root 8) 0 1 :=
  of_native_maps core0968 DegreeOneSmallSpectrum535.graph DegreeOneSmallSpectrum585.graph
    sourceMap0968 fusedMap0968 sourceMap0968_checked fusedMap0968_checked
    DegreeOneSmallComparisons.comparison0968
#print axioms sourceMap0968_checked
#print axioms fusedMap0968_checked
#print axioms certified0968
def sourceMap0968swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0968swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (fusedLabel 8 1 0 v)
theorem sourceMap0968swap_checked : acceptsGraphIso
    (source (graph core0968) (root 8) 1 0) DegreeOneSmallSpectrum535.graph sourceMap0968swap=true := by decide +kernel
theorem fusedMap0968swap_checked : acceptsGraphIso
    (fused (graph core0968) (root 8) 1 0) DegreeOneSmallSpectrum585.graph fusedMap0968swap=true := by decide +kernel
theorem certified0968swap : Certified (graph core0968) (root 8) 1 0 :=
  of_native_maps core0968 DegreeOneSmallSpectrum535.graph DegreeOneSmallSpectrum585.graph
    sourceMap0968swap fusedMap0968swap sourceMap0968swap_checked fusedMap0968swap_checked
    DegreeOneSmallComparisons.comparison0968
#print axioms sourceMap0968swap_checked
#print axioms fusedMap0968swap_checked
#print axioms certified0968swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
