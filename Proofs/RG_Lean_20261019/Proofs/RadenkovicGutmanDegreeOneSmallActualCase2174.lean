/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2174 : Family 10 := level10.get ⟨654,by decide⟩
def sourceMap2174 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (sourceLabel 10 0 0 v)
def fusedMap2174 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2174_checked : acceptsGraphIso
    (source (graph core2174) (root 10) 0 0) DegreeOneSmallSpectrum1192.graph sourceMap2174=true := by decide +kernel
theorem fusedMap2174_checked : acceptsGraphIso
    (fused (graph core2174) (root 10) 0 0) DegreeOneSmallSpectrum1186.graph fusedMap2174=true := by decide +kernel
theorem certified2174 : Certified (graph core2174) (root 10) 0 0 :=
  of_native_maps core2174 DegreeOneSmallSpectrum1192.graph DegreeOneSmallSpectrum1186.graph
    sourceMap2174 fusedMap2174 sourceMap2174_checked fusedMap2174_checked
    DegreeOneSmallComparisons.comparison2174
#print axioms sourceMap2174_checked
#print axioms fusedMap2174_checked
#print axioms certified2174
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
