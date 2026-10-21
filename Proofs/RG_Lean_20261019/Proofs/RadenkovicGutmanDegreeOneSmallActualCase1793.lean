/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1793 : Family 10 := level10.get ⟨29,by decide⟩
def sourceMap1793 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1793 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1793_checked : acceptsGraphIso
    (source (graph core1793) (root 10) 0 0) DegreeOneSmallSpectrum892.graph sourceMap1793=true := by decide +kernel
theorem fusedMap1793_checked : acceptsGraphIso
    (fused (graph core1793) (root 10) 0 0) DegreeOneSmallSpectrum966.graph fusedMap1793=true := by decide +kernel
theorem certified1793 : Certified (graph core1793) (root 10) 0 0 :=
  of_native_maps core1793 DegreeOneSmallSpectrum892.graph DegreeOneSmallSpectrum966.graph
    sourceMap1793 fusedMap1793 sourceMap1793_checked fusedMap1793_checked
    DegreeOneSmallComparisons.comparison1793
#print axioms sourceMap1793_checked
#print axioms fusedMap1793_checked
#print axioms certified1793
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
