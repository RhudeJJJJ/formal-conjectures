/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0595 : Family 7 := level7.get ⟨32,by decide⟩
def sourceMap0595 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (sourceLabel 7 1 1 v)
def fusedMap0595 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0595_checked : acceptsGraphIso
    (source (graph core0595) (root 7) 1 1) DegreeOneSmallSpectrum735.graph sourceMap0595=true := by decide +kernel
theorem fusedMap0595_checked : acceptsGraphIso
    (fused (graph core0595) (root 7) 1 1) DegreeOneSmallSpectrum446.graph fusedMap0595=true := by decide +kernel
theorem certified0595 : Certified (graph core0595) (root 7) 1 1 :=
  of_native_maps core0595 DegreeOneSmallSpectrum735.graph DegreeOneSmallSpectrum446.graph
    sourceMap0595 fusedMap0595 sourceMap0595_checked fusedMap0595_checked
    DegreeOneSmallComparisons.comparison0595
#print axioms sourceMap0595_checked
#print axioms fusedMap0595_checked
#print axioms certified0595
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
