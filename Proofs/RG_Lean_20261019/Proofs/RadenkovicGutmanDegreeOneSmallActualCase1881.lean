/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1881 : Family 10 := level10.get ⟨147,by decide⟩
def sourceMap1881 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (sourceLabel 10 0 0 v)
def fusedMap1881 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1881_checked : acceptsGraphIso
    (source (graph core1881) (root 10) 0 0) DegreeOneSmallSpectrum1290.graph sourceMap1881=true := by decide +kernel
theorem fusedMap1881_checked : acceptsGraphIso
    (fused (graph core1881) (root 10) 0 0) DegreeOneSmallSpectrum969.graph fusedMap1881=true := by decide +kernel
theorem certified1881 : Certified (graph core1881) (root 10) 0 0 :=
  of_native_maps core1881 DegreeOneSmallSpectrum1290.graph DegreeOneSmallSpectrum969.graph
    sourceMap1881 fusedMap1881 sourceMap1881_checked fusedMap1881_checked
    DegreeOneSmallComparisons.comparison1881
#print axioms sourceMap1881_checked
#print axioms fusedMap1881_checked
#print axioms certified1881
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
