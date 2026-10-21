/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1934 : Family 10 := level10.get ⟨228,by decide⟩
def sourceMap1934 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1934 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1934_checked : acceptsGraphIso
    (source (graph core1934) (root 10) 0 0) DegreeOneSmallSpectrum1149.graph sourceMap1934=true := by decide +kernel
theorem fusedMap1934_checked : acceptsGraphIso
    (fused (graph core1934) (root 10) 0 0) DegreeOneSmallSpectrum1158.graph fusedMap1934=true := by decide +kernel
theorem certified1934 : Certified (graph core1934) (root 10) 0 0 :=
  of_native_maps core1934 DegreeOneSmallSpectrum1149.graph DegreeOneSmallSpectrum1158.graph
    sourceMap1934 fusedMap1934 sourceMap1934_checked fusedMap1934_checked
    DegreeOneSmallComparisons.comparison1934
#print axioms sourceMap1934_checked
#print axioms fusedMap1934_checked
#print axioms certified1934
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
