/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0453 : Family 7 := level7.get ⟨1,by decide⟩
def sourceMap0453 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,5,6,7,8,9,3,4] (sourceLabel 7 0 0 v)
def fusedMap0453 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0453_checked : acceptsGraphIso
    (source (graph core0453) (root 7) 0 0) DegreeOneSmallSpectrum077.graph sourceMap0453=true := by decide +kernel
theorem fusedMap0453_checked : acceptsGraphIso
    (fused (graph core0453) (root 7) 0 0) DegreeOneSmallSpectrum080.graph fusedMap0453=true := by decide +kernel
theorem certified0453 : Certified (graph core0453) (root 7) 0 0 :=
  of_native_maps core0453 DegreeOneSmallSpectrum077.graph DegreeOneSmallSpectrum080.graph
    sourceMap0453 fusedMap0453 sourceMap0453_checked fusedMap0453_checked
    DegreeOneSmallComparisons.comparison0453
#print axioms sourceMap0453_checked
#print axioms fusedMap0453_checked
#print axioms certified0453
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
