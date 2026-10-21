/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1825 : Family 10 := level10.get ⟨70,by decide⟩
def sourceMap1825 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1825 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1825_checked : acceptsGraphIso
    (source (graph core1825) (root 10) 0 0) DegreeOneSmallSpectrum1227.graph sourceMap1825=true := by decide +kernel
theorem fusedMap1825_checked : acceptsGraphIso
    (fused (graph core1825) (root 10) 0 0) DegreeOneSmallSpectrum886.graph fusedMap1825=true := by decide +kernel
theorem certified1825 : Certified (graph core1825) (root 10) 0 0 :=
  of_native_maps core1825 DegreeOneSmallSpectrum1227.graph DegreeOneSmallSpectrum886.graph
    sourceMap1825 fusedMap1825 sourceMap1825_checked fusedMap1825_checked
    DegreeOneSmallComparisons.comparison1825
#print axioms sourceMap1825_checked
#print axioms fusedMap1825_checked
#print axioms certified1825
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
