/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0063 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0063 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,5,6,7,1,2,3,4] (sourceLabel 3 1 1 v)
def fusedMap0063 : (Vertices 3 ⊕ Fin 4) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 3 1 1 v)
theorem sourceMap0063_checked : acceptsGraphIso
    (source (graph core0063) (root 3) 1 1) DegreeOneSmallSpectrum022.graph sourceMap0063=true := by decide +kernel
theorem fusedMap0063_checked : acceptsGraphIso
    (fused (graph core0063) (root 3) 1 1) DegreeOneSmallSpectrum016.graph fusedMap0063=true := by decide +kernel
theorem certified0063 : Certified (graph core0063) (root 3) 1 1 :=
  of_native_maps core0063 DegreeOneSmallSpectrum022.graph DegreeOneSmallSpectrum016.graph
    sourceMap0063 fusedMap0063 sourceMap0063_checked fusedMap0063_checked
    DegreeOneSmallComparisons.comparison0063
#print axioms sourceMap0063_checked
#print axioms fusedMap0063_checked
#print axioms certified0063
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
