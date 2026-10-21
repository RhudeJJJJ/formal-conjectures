/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0393 : Family 6 := level6.get ⟨20,by decide⟩
def sourceMap0393 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,8,6,7] (sourceLabel 6 0 0 v)
def fusedMap0393 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![6,0,1,2,3,4,5,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0393_checked : acceptsGraphIso
    (source (graph core0393) (root 6) 0 0) DegreeOneSmallSpectrum067.graph sourceMap0393=true := by decide +kernel
theorem fusedMap0393_checked : acceptsGraphIso
    (fused (graph core0393) (root 6) 0 0) DegreeOneSmallSpectrum039.graph fusedMap0393=true := by decide +kernel
theorem certified0393 : Certified (graph core0393) (root 6) 0 0 :=
  of_native_maps core0393 DegreeOneSmallSpectrum067.graph DegreeOneSmallSpectrum039.graph
    sourceMap0393 fusedMap0393 sourceMap0393_checked fusedMap0393_checked
    DegreeOneSmallComparisons.comparison0393
#print axioms sourceMap0393_checked
#print axioms fusedMap0393_checked
#print axioms certified0393
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
