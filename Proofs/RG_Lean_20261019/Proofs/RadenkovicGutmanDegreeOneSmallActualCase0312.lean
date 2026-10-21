/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0312 : Family 6 := level6.get ⟨6,by decide⟩
def sourceMap0312 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![6,5,0,1,2,3,4,7,8] (sourceLabel 6 0 0 v)
def fusedMap0312 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![6,0,1,2,3,4,5,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0312_checked : acceptsGraphIso
    (source (graph core0312) (root 6) 0 0) DegreeOneSmallSpectrum040.graph sourceMap0312=true := by decide +kernel
theorem fusedMap0312_checked : acceptsGraphIso
    (fused (graph core0312) (root 6) 0 0) DegreeOneSmallSpectrum042.graph fusedMap0312=true := by decide +kernel
theorem certified0312 : Certified (graph core0312) (root 6) 0 0 :=
  of_native_maps core0312 DegreeOneSmallSpectrum040.graph DegreeOneSmallSpectrum042.graph
    sourceMap0312 fusedMap0312 sourceMap0312_checked fusedMap0312_checked
    DegreeOneSmallComparisons.comparison0312
#print axioms sourceMap0312_checked
#print axioms fusedMap0312_checked
#print axioms certified0312
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
