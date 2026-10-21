/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1948 : Family 10 := level10.get ⟨248,by decide⟩
def sourceMap1948 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1948 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1948_checked : acceptsGraphIso
    (source (graph core1948) (root 10) 0 0) DegreeOneSmallSpectrum1161.graph sourceMap1948=true := by decide +kernel
theorem fusedMap1948_checked : acceptsGraphIso
    (fused (graph core1948) (root 10) 0 0) DegreeOneSmallSpectrum1225.graph fusedMap1948=true := by decide +kernel
theorem certified1948 : Certified (graph core1948) (root 10) 0 0 :=
  of_native_maps core1948 DegreeOneSmallSpectrum1161.graph DegreeOneSmallSpectrum1225.graph
    sourceMap1948 fusedMap1948 sourceMap1948_checked fusedMap1948_checked
    DegreeOneSmallComparisons.comparison1948
#print axioms sourceMap1948_checked
#print axioms fusedMap1948_checked
#print axioms certified1948
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
