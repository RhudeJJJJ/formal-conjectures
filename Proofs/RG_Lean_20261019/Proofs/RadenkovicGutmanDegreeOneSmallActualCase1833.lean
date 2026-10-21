/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1833 : Family 10 := level10.get ⟨80,by decide⟩
def sourceMap1833 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1833 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1833_checked : acceptsGraphIso
    (source (graph core1833) (root 10) 0 0) DegreeOneSmallSpectrum1150.graph sourceMap1833=true := by decide +kernel
theorem fusedMap1833_checked : acceptsGraphIso
    (fused (graph core1833) (root 10) 0 0) DegreeOneSmallSpectrum903.graph fusedMap1833=true := by decide +kernel
theorem certified1833 : Certified (graph core1833) (root 10) 0 0 :=
  of_native_maps core1833 DegreeOneSmallSpectrum1150.graph DegreeOneSmallSpectrum903.graph
    sourceMap1833 fusedMap1833 sourceMap1833_checked fusedMap1833_checked
    DegreeOneSmallComparisons.comparison1833
#print axioms sourceMap1833_checked
#print axioms fusedMap1833_checked
#print axioms certified1833
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
