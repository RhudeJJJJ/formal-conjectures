/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1780 : Family 10 := level10.get ⟨14,by decide⟩
def sourceMap1780 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1780 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1780_checked : acceptsGraphIso
    (source (graph core1780) (root 10) 0 0) DegreeOneSmallSpectrum890.graph sourceMap1780=true := by decide +kernel
theorem fusedMap1780_checked : acceptsGraphIso
    (fused (graph core1780) (root 10) 0 0) DegreeOneSmallSpectrum908.graph fusedMap1780=true := by decide +kernel
theorem certified1780 : Certified (graph core1780) (root 10) 0 0 :=
  of_native_maps core1780 DegreeOneSmallSpectrum890.graph DegreeOneSmallSpectrum908.graph
    sourceMap1780 fusedMap1780 sourceMap1780_checked fusedMap1780_checked
    DegreeOneSmallComparisons.comparison1780
#print axioms sourceMap1780_checked
#print axioms fusedMap1780_checked
#print axioms certified1780
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
