/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0225 : Family 5 := level5.get ⟨6,by decide⟩
def sourceMap0225 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9] (sourceLabel 5 1 1 v)
def fusedMap0225 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap0225_checked : acceptsGraphIso
    (source (graph core0225) (root 5) 1 1) DegreeOneSmallSpectrum118.graph sourceMap0225=true := by decide +kernel
theorem fusedMap0225_checked : acceptsGraphIso
    (fused (graph core0225) (root 5) 1 1) DegreeOneSmallSpectrum075.graph fusedMap0225=true := by decide +kernel
theorem certified0225 : Certified (graph core0225) (root 5) 1 1 :=
  of_native_maps core0225 DegreeOneSmallSpectrum118.graph DegreeOneSmallSpectrum075.graph
    sourceMap0225 fusedMap0225 sourceMap0225_checked fusedMap0225_checked
    DegreeOneSmallComparisons.comparison0225
#print axioms sourceMap0225_checked
#print axioms fusedMap0225_checked
#print axioms certified0225
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
