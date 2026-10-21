/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1983 : Family 10 := level10.get ⟨307,by decide⟩
def sourceMap1983 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1983 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1983_checked : acceptsGraphIso
    (source (graph core1983) (root 10) 0 0) DegreeOneSmallSpectrum1167.graph sourceMap1983=true := by decide +kernel
theorem fusedMap1983_checked : acceptsGraphIso
    (fused (graph core1983) (root 10) 0 0) DegreeOneSmallSpectrum1363.graph fusedMap1983=true := by decide +kernel
theorem certified1983 : Certified (graph core1983) (root 10) 0 0 :=
  of_native_maps core1983 DegreeOneSmallSpectrum1167.graph DegreeOneSmallSpectrum1363.graph
    sourceMap1983 fusedMap1983 sourceMap1983_checked fusedMap1983_checked
    DegreeOneSmallComparisons.comparison1983
#print axioms sourceMap1983_checked
#print axioms fusedMap1983_checked
#print axioms certified1983
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
