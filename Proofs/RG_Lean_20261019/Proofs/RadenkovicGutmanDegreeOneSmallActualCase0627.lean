/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0627 : Family 7 := level7.get ⟨43,by decide⟩
def sourceMap0627 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,4,2,3] (sourceLabel 7 0 0 v)
def fusedMap0627 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0627_checked : acceptsGraphIso
    (source (graph core0627) (root 7) 0 0) DegreeOneSmallSpectrum119.graph sourceMap0627=true := by decide +kernel
theorem fusedMap0627_checked : acceptsGraphIso
    (fused (graph core0627) (root 7) 0 0) DegreeOneSmallSpectrum142.graph fusedMap0627=true := by decide +kernel
theorem certified0627 : Certified (graph core0627) (root 7) 0 0 :=
  of_native_maps core0627 DegreeOneSmallSpectrum119.graph DegreeOneSmallSpectrum142.graph
    sourceMap0627 fusedMap0627 sourceMap0627_checked fusedMap0627_checked
    DegreeOneSmallComparisons.comparison0627
#print axioms sourceMap0627_checked
#print axioms fusedMap0627_checked
#print axioms certified0627
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
