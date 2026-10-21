/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0058 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0058 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 3 0 3 v)
def fusedMap0058 : (Vertices 3 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,2,3,4,0,5,6,7,8] (fusedLabel 3 0 3 v)
theorem sourceMap0058_checked : acceptsGraphIso
    (source (graph core0058) (root 3) 0 3) DegreeOneSmallSpectrum036.graph sourceMap0058=true := by decide +kernel
theorem fusedMap0058_checked : acceptsGraphIso
    (fused (graph core0058) (root 3) 0 3) DegreeOneSmallSpectrum037.graph fusedMap0058=true := by decide +kernel
theorem certified0058 : Certified (graph core0058) (root 3) 0 3 :=
  of_native_maps core0058 DegreeOneSmallSpectrum036.graph DegreeOneSmallSpectrum037.graph
    sourceMap0058 fusedMap0058 sourceMap0058_checked fusedMap0058_checked
    DegreeOneSmallComparisons.comparison0058
#print axioms sourceMap0058_checked
#print axioms fusedMap0058_checked
#print axioms certified0058
def sourceMap0058swap : (Vertices 3 ⊕ Fin 4 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,5,6,7,8,4] (sourceLabel 3 3 0 v)
def fusedMap0058swap : (Vertices 3 ⊕ Fin 5) → Fin 9 :=
  fun v => ![1,2,3,4,0,5,6,7,8] (fusedLabel 3 3 0 v)
theorem sourceMap0058swap_checked : acceptsGraphIso
    (source (graph core0058) (root 3) 3 0) DegreeOneSmallSpectrum036.graph sourceMap0058swap=true := by decide +kernel
theorem fusedMap0058swap_checked : acceptsGraphIso
    (fused (graph core0058) (root 3) 3 0) DegreeOneSmallSpectrum037.graph fusedMap0058swap=true := by decide +kernel
theorem certified0058swap : Certified (graph core0058) (root 3) 3 0 :=
  of_native_maps core0058 DegreeOneSmallSpectrum036.graph DegreeOneSmallSpectrum037.graph
    sourceMap0058swap fusedMap0058swap sourceMap0058swap_checked fusedMap0058swap_checked
    DegreeOneSmallComparisons.comparison0058
#print axioms sourceMap0058swap_checked
#print axioms fusedMap0058swap_checked
#print axioms certified0058swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
