/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1784 : Family 10 := level10.get ⟨19,by decide⟩
def sourceMap1784 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1784 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1784_checked : acceptsGraphIso
    (source (graph core1784) (root 10) 0 0) DegreeOneSmallSpectrum897.graph sourceMap1784=true := by decide +kernel
theorem fusedMap1784_checked : acceptsGraphIso
    (fused (graph core1784) (root 10) 0 0) DegreeOneSmallSpectrum922.graph fusedMap1784=true := by decide +kernel
theorem certified1784 : Certified (graph core1784) (root 10) 0 0 :=
  of_native_maps core1784 DegreeOneSmallSpectrum897.graph DegreeOneSmallSpectrum922.graph
    sourceMap1784 fusedMap1784 sourceMap1784_checked fusedMap1784_checked
    DegreeOneSmallComparisons.comparison1784
#print axioms sourceMap1784_checked
#print axioms fusedMap1784_checked
#print axioms certified1784
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
