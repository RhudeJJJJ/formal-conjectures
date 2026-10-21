/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1955 : Family 10 := level10.get ⟨260,by decide⟩
def sourceMap1955 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap1955 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap1955_checked : acceptsGraphIso
    (source (graph core1955) (root 10) 0 0) DegreeOneSmallSpectrum1192.graph sourceMap1955=true := by decide +kernel
theorem fusedMap1955_checked : acceptsGraphIso
    (fused (graph core1955) (root 10) 0 0) DegreeOneSmallSpectrum1289.graph fusedMap1955=true := by decide +kernel
theorem certified1955 : Certified (graph core1955) (root 10) 0 0 :=
  of_native_maps core1955 DegreeOneSmallSpectrum1192.graph DegreeOneSmallSpectrum1289.graph
    sourceMap1955 fusedMap1955 sourceMap1955_checked fusedMap1955_checked
    DegreeOneSmallComparisons.comparison1955
#print axioms sourceMap1955_checked
#print axioms fusedMap1955_checked
#print axioms certified1955
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
