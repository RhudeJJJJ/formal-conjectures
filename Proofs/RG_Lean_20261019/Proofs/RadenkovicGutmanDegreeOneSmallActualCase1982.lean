/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1982 : Family 10 := level10.get ⟨306,by decide⟩
def sourceMap1982 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1982 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1982_checked : acceptsGraphIso
    (source (graph core1982) (root 10) 0 0) DegreeOneSmallSpectrum1232.graph sourceMap1982=true := by decide +kernel
theorem fusedMap1982_checked : acceptsGraphIso
    (fused (graph core1982) (root 10) 0 0) DegreeOneSmallSpectrum1364.graph fusedMap1982=true := by decide +kernel
theorem certified1982 : Certified (graph core1982) (root 10) 0 0 :=
  of_native_maps core1982 DegreeOneSmallSpectrum1232.graph DegreeOneSmallSpectrum1364.graph
    sourceMap1982 fusedMap1982 sourceMap1982_checked fusedMap1982_checked
    DegreeOneSmallComparisons.comparison1982
#print axioms sourceMap1982_checked
#print axioms fusedMap1982_checked
#print axioms certified1982
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
