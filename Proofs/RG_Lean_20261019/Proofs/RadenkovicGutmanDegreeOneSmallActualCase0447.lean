/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0447 : Family 7 := level7.get ⟨0,by decide⟩
def sourceMap0447 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![3,2,1,0,6,7,8,9,4,5] (sourceLabel 7 0 0 v)
def fusedMap0447 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![2,1,0,5,6,7,8,9,3,4] (fusedLabel 7 0 0 v)
theorem sourceMap0447_checked : acceptsGraphIso
    (source (graph core0447) (root 7) 0 0) DegreeOneSmallSpectrum080.graph sourceMap0447=true := by decide +kernel
theorem fusedMap0447_checked : acceptsGraphIso
    (fused (graph core0447) (root 7) 0 0) DegreeOneSmallSpectrum073.graph fusedMap0447=true := by decide +kernel
theorem certified0447 : Certified (graph core0447) (root 7) 0 0 :=
  of_native_maps core0447 DegreeOneSmallSpectrum080.graph DegreeOneSmallSpectrum073.graph
    sourceMap0447 fusedMap0447 sourceMap0447_checked fusedMap0447_checked
    DegreeOneSmallComparisons.comparison0447
#print axioms sourceMap0447_checked
#print axioms fusedMap0447_checked
#print axioms certified0447
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
