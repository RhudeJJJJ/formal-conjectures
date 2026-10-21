/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0285 : Family 6 := level6.get ⟨2,by decide⟩
def sourceMap0285 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![2,1,0,5,6,7,8,3,4] (sourceLabel 6 0 0 v)
def fusedMap0285 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![6,5,0,1,2,3,4,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0285_checked : acceptsGraphIso
    (source (graph core0285) (root 6) 0 0) DegreeOneSmallSpectrum051.graph sourceMap0285=true := by decide +kernel
theorem fusedMap0285_checked : acceptsGraphIso
    (fused (graph core0285) (root 6) 0 0) DegreeOneSmallSpectrum035.graph fusedMap0285=true := by decide +kernel
theorem certified0285 : Certified (graph core0285) (root 6) 0 0 :=
  of_native_maps core0285 DegreeOneSmallSpectrum051.graph DegreeOneSmallSpectrum035.graph
    sourceMap0285 fusedMap0285 sourceMap0285_checked fusedMap0285_checked
    DegreeOneSmallComparisons.comparison0285
#print axioms sourceMap0285_checked
#print axioms fusedMap0285_checked
#print axioms certified0285
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
